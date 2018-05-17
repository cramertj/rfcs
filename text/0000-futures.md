- Feature Name: futures
- Start Date: 2018-05-16)
- RFC PR: (leave this empty)
- Rust Issue: (leave this empty)

# Summary
[summary]: #summary

Add a `Future` trait to `core`. Implement the `Future` trait for the anonymous type returned by
`async` functions and `async` blocks (introduced in [RFC 2394][2394]).

[2394]: https://github.com/rust-lang/rfcs/blob/master/text/2394-async_await.md

# Motivation
[motivation]: #motivation

The motivation for `async`/`await` syntax is described in detail in [RFC 2394][2394].
In short, `async`/`await` makes it possible to create complex self-borrowing state-machine types
via simpler straight-line code.

Supporting language-level `async`/`await` syntax requires including a `Future` abstraction
in `core` so that the compiler can desugar `async` functions and `async` blocks into definitions
of anonymous types that implement the `Future` trait, much like closures implement the `Fn` traits:

```rust
async fn foo(x: &str) -> usize {
    x.len()
}

// is equivalent to the following:

fn foo<'a>(x: &'a str) -> impl Future<Output = usize> + 'a {
    _Anon(x)
}

struct _Anon<'a> {
    x: &'a str,
}

impl<'a> Future for Anon<'a> {
    type Output = usize;
    fn poll_pinned(self: PinMut<Self>) -> Poll<Self::Output> {
        Poll::Ready(self.x.len())
    }
}
```


# Guide-level explanation
[guide-level-explanation]: #guide-level-explanation

`core` now includes a trait called `Future` for working with asynchronous operations:

```rust
pub trait Future {
    type Output;
    fn poll_pinned(self: PinMut<Self>, cx: &mut task::Context) -> Poll<Self::Output>;
}
```

The `Future::poll` method checks if the future is complete and returns the value if it is available.
If no result is available, it schedules the current task to be woken up when the `Future::poll`
should be called again to make progress.

`async fn` and `async` blocks return anonymous types that implement `Future`.

`core` also includes a trait called `MoveFuture`:

```rust
// NB: the `Unpin` bound below is needed for the blanket implementation of `Future` for `MoveFuture`.
pub trait MoveFuture: Unpin {
    type Output;
    fn poll(&mut self) -> Self::Output;
}
```

This trait is similar to `Future`, but is designed to be used in manual implementations of
`Future` that wish to avoid the hairy details of working with `PinMut`.
Types that implement `MoveFuture` automatically implement `Future`.
If you have a `Future` and want a `MoveFuture`, you can use one of two approaches:
- `Future` types that are `Unpin` can be converted to `MoveFuture` via an `into_move_future` method.
- Any `Future` contained in a `PinMut` or `PinBox` automatically implements `MoveFuture`.

Finally, it's common for futures to return `Result` types to indicate that an error may occur.
To make this case more ergonomic, there are two corresponding traits, `TryFuture` and
`TryMoveFuture` for working with the fallible cases:

```rust
pub trait TryFuture {
    type Item;
    type Error;
    fn try_poll_pinned(self: PinMut<Self>, cx: &mut task::Context)
        -> Poll<Result<Self::Item, Self::Error>>;
}

pub trait TryMoveFuture {
    type Item;
    type Error;
    fn try_poll(&mut self, cx: &mut task::Context)
        -> Poll<Result<Self::Item, Self::Error>>;
}
```

The `TryFuture` and `TryMoveFuture` traits are automatically implemented by `Future` and
`MoveFuture` types that yield `Result`. These traits will be included in the `futures` crate,
as it is possible to define them outside of the standard library.

# Reference-level explanation
[reference-level-explanation]: #reference-level-explanation

## The `task` Module
[reference-task-module]: #reference-task-module

The fundamental unit of asynchronous computation in Rust is a task.
Tasks are which are lightweight, cooperatively scheduled threads of execution.
Many tasks can be run on a single operating system thread.

When a task can no longer make progress until some event occurs, it schedules itself for
wakeup on that event and returns control to the executor which ran the task.
The executor is then free to run other tasks. Subsequent wakeups place the task back on
the executor's queue of ready tasks, much like a thread scheduler in an operating system.

Attempting to complete a task or an asynchronous operation within a task will yield a `Poll`
value:

```rust
/// Indicates whether a value is available or if the current task has been scheduled for
/// later wake-up instead.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Poll<T> {
    /// Represents that a value is immediately ready.
    Ready(T),

    /// Represents that a value is not ready yet.
    ///
    /// When a function returns `Pending`, the function *must* also
    /// ensure that the current task is scheduled to be awoken when
    /// progress can be made.
    Pending,
}

### Waking up

Each task executor provides its own scheduling facilities, and hence needs to
customize the way task wakeups are handled. As such, there is a
`std::task::Wake` trait defining wakeup behavior:

```rust
/// A way of waking up a specific task.
///
/// Any task executor must provide a way of signaling that a task it owns
/// is ready to be `poll`ed again. Executors do so by providing a wakeup handle
/// type that implements this trait.
pub trait Wake: Send + Sync {
    /// Indicates that the associated task is ready to make progress and should
    /// be `poll`ed.
    ///
    /// Executors generally maintain a queue of "ready" tasks; `wake` should place
    /// the associated task onto this queue.
    fn wake(arc_self: &Arc<Self>);
}
```

In general async values are not coupled to any particular executor, so we use a trait
object to handle waking:

```rust
/// A `Waker` is a handle for waking up a task by notifying its executor that it
/// is ready to be run.
///
/// This handle contains a trait object pointing to an instance of the `UnsafeWake`
/// trait, allowing notifications to get routed through it.
///
/// Implements `Clone`, `Send`, and `Sync`.
pub struct Waker { ... }

/// A `Waker` is a handle for waking up a task by notifying its executor that it is
/// ready to be run.
///
/// Unlike `Waker`, `LocalWaker` is neither `Send` nor `Sync`, and so can only be used
/// from the thread on which the `LocalWaker` was acquired.
///
/// Implements `Clone`.
pub struct LocalWaker { ... }

impl Waker {
    /// Wake up the task associated with this `Waker`.
    pub fn wake(&self);
}

impl LocalWaker {
    /// Wake up the task associated with this `LocalWaker`.
    pub fn wake(&self);

    /// Get a reference to an interior `Waker` inside of the  `LocalWaker`
    /// that can be used to wake up the task from a separate thread.
    pub fn waker(&self) -> &Waker;
}

// We will see how to handle the no_std case later in the RFC...
impl<T> From<T> for Waker where Arc<T>: Wake + 'static { ... }
```

Task execution always happens in the context of a `Waker` that can be used to
wake the task up; we'll see the full `core::task::Context` structure below.

`LocalWaker` is included to support executors which want to include optimized task queues
for the single-threaded execution case
(e.g. by including a per-thread `Rc<RefCell<Queue<Task>>>` rather than just a single
`Arc<FancyLockFreeQueue<Task>>`). Even in these optimized cases, it should be possible
to fall back to a non-thread-local task queue when necessary, so `LocalWaker`s should
always be convertible into `Waker`s.

### Executors

An executor is responsible for polling tasks to completion. We represent this
with the `core::task::Executor` trait:

```rust
/// A task executor.
///
/// A *task* is a `()`-producing async value that runs at the top level, and will
/// be `poll`ed until completion. It's also the unit at which wake-up
/// notifications occur. Executors, such as thread pools, allow tasks to be
/// spawned and are responsible for putting tasks onto ready queues when
/// they are woken up, and polling them when they are ready.
pub trait Executor {
    /// Spawn the given task, polling it until completion.
    ///
    /// # Errors
    ///
    /// The executor may be unable to spawn tasks, either because it has
    /// been shut down or is resource-constrained.
    fn spawn_obj(&mut self, task: TaskObj) -> Result<(), SpawnObjError>;

    /// Determine whether the executor is able to spawn new tasks.
    ///
    /// # Returns
    ///
    /// An `Ok` return means the executor is *likely* (but not guaranteed)
    /// to accept a subsequent spawn attempt. Likewise, an `Err` return
    /// means that `spawn` is likely, but not guaranteed, to yield an error.
    fn status(&self) -> Result<(), SpawnErrorKind> {
        Ok(())
    }
}

pub struct TaskObj { .. }

impl TaskObj {
    /// Create a new `TaskObj` by boxing the given future.
    pub fn new<A: Async<Output = ()> + Send + 'static>(f: A) -> TaskObj;
}

/// Provides the reason that an executor was unable to spawn.
pub struct SpawnErrorKind { .. }

impl SpawnErrorKind {
    /// Spawning is failing because the executor has been shut down.
    pub fn shutdown() -> SpawnErrorKind;

    /// Check whether this error is the `shutdown` error.
    pub fn is_shutdown(&self) -> bool;

    // additional error variants added over time...
}

/// The result of a failed spawn
pub struct SpawnObjError {
    /// The kind of error
    pub kind: SpawnErrorKind,

    /// The task for which spawning was attempted
    pub task: TaskObj,
}
```

We need the executor trait to be usable as a trait object, which is why `TaskObj`
is constructed here from a boxed future. (In the no_std section, we'll see
another constructor). In the long run, though, once we can take `dyn` by value,
we would deprecate `spawn_obj` and add a default `spawn` method:

```rust
trait Executor {
    fn spawn(&mut self, task: Async<Output = ()> + Send) -> Result<(), SpawnErrorKind> {
        self.spawn_obj(TaskObj::new(task))
    }
    // ...
}
```

At that point we would also deprecate `TaskObj`, which is the reason for using
the `Obj` suffix -- we want to keep the name `Task` available for potential
usage down the line.

In addition to the above, the `core::task` module will include the following API
for helping detect bugs:

```rust
/// Marks the current thread as being within the dynamic extent of an
/// executor.
///
/// Executor implementations should call this function before beginning to
/// execute a tasks, and drop the returned `Enter` value after completing
/// task execution:
///
/// ```rust
/// let enter = enter().expect("...");
/// /* run task */
/// drop(enter);
/// ```
///
/// Doing so ensures that executors aren't accidentally invoked in a nested fashion.
/// When that happens, the inner executor can block waiting for an event that can
/// only be triggered by the outer executor, leading to a deadlock.
///
/// # Error
///
/// Returns an error if the current thread is already marked, in which case the
/// caller should panic with a tailored error message.
pub fn enter() -> Result<Enter, EnterError>
```

As stated in the doc comment, the expectation is that all executors will wrap
their task execution within an `enter` to detect inadvertent nesting.

Note that this spawning functionality does *not* provide the ability to spawn
non-`Send` tasks. While non-`Send` tasks can allow for an additional level of
optimization (especially when paired with `LocalWaker`), operating system constraints
make it impossible to support thread-fixed task spawning in a cross-platform way.
Doing so would require the ability to wake a *specific* thread based on a given `epoll`,
`kqueue`, `iocp`, or `zx_port` event while simultaneously supporting the ability for
*some* events to wake up *any* thread. Some platforms do support this capability,
such as some recent versions of Linux which provide EPOLLEXCLUSIVE. These systems
can provide access to thread-local spawning via TLS. Since this ability is not
universally supported, it cannot be baked into the task context.

### Task contexts

All tasks are executed with two pieces of contextual information:

- A `Waker` for waking the task up later on.
- An executor, which is the "default" place to spawn further tasks.

Notably, this list does *not* include task-local data; that can be addressed
externally, as we'll see in a later section.

The `core::task::Context` type gathers the (stack-rooted) contextual information
together, and is passed by mutable reference to all polling functions:

```rust
/// Information about the currently-running task.
///
/// Contexts are always tied to the stack, since they are set up specifically
/// when performing a single `poll` step on a task.
pub struct Context<'a> { .. }

impl<'a> Context<'a> {
    pub fn new(waker: &'a Waker, executor: &'a mut Executor) -> Context<'a>

    /// Get the `LocalWaker` associated with the current task.
    pub fn local_waker(&self) -> &Waker;

    /// Get the `Waker` associated with the current task.
    pub fn waker(&self) -> &Waker;

    /// Run an asynchronous computation to completion on the default executor.
    ///
    /// # Panics
    ///
    /// This method will panic if the default executor is unable to spawn.
    /// To handle executor errors, use the `executor` method instead.
    pub fn spawn(&mut self, f: impl Future<Output = ()> + 'static + Send);

    /// Get the default executor associated with this task.
    ///
    /// This method is useful primarily if you want to explicitly handle
    /// spawn failures.
    ///
    /// NB: this will remain unstable until the final `Executor` trait is ready.
    pub fn executor(&mut self) -> &mut BoxExecutor;
}
```

Note that the `spawn` method here will box until `Executor` is added.

## `Future` and `MoveFuture`
[reference-future-and-move]: #reference-future-and-move

Previous RFCs have proposed a single `Future` trait, rather than two separate traits.
In many ways, this seems like a clear solution since implementaiton of the `Unpin` trait
determines whether or not the `Future` is movable, so an extra trait isn't strictly necessary.
However, this approach makes manual implementations of movable-only futures less ergonomic,
since it forces them to add an explicit `Unpin` bound to all of their child futures in order
to safely poll them, and polling them requires wrapping them in a call to `PinMut::new`.
These steps add unnecessary complication for users who aren't working with immovable futures.

Here's an example of what implementing a safe, movable future looks like with and without
the separate `MoveFuture` trait:

```rust
pub struct Map<Fut, F> {
    future: Fut,
    f: Option<F>,
}

// We don't ever unsafely project `PinMut<Map<Fut, F>>` to `PinMut<Fut>` or `PinMut<F>`,
// so we can opt into `Unpin` unconditionally.
impl<Fut, F> Unpin for Map<Fut, F> {}

// Without `MoveFuture`:
impl<Fut, F, U> Future for Map<Fut, F>
    where Fut: Future + Unpin,
          F: FnOnce(Fut::Output) -> U
{
    type Output = U;

    fn poll(self: PinMut<Self>, cx: &mut task::Context) -> Poll<Self::Output> {
        let result = match PinMut::new(&mut self.future).poll(cx) {
            Poll::Ready(x) => x,
            Poll::Pending => return Poll::Pending,
        };
        let f = self.f.take().expect("Map polled after completion");
        Poll::Ready((f)(result))
    }
}

// With `MoveFuture`:
impl<Fut, F, U> Future for Map<Fut, F>
    where Fut: MoveFuture,
          F: FnOnce(Fut::Output> -> U,
{
    type Output = U;

    fn poll(&mut self, cx: &mut task::Context) -> Poll<Self::Output> {
        let result = match self.future.poll(cx) {
            Poll::Ready(x) => x,
            Poll::Pending => return Poll::Pending,
        };
        let f = self.f.take().expect("Map polled after completion");
        Poll::Ready((f)(result))       
    }
}
```

The primary differences are:
- The bound on child futures is shortened from `Future + Unpin` to `MoveFuture`.
- `poll` takes `&mut self` rather than `PinMut<Self>`, which is a more familiar type to
  Rust users.
- There's no more need to wrap the child future in `PinMut::new(&mut self.future)` before
  polling.

As mentioned in the guide-level section, types that implement `MoveFuture` automatically
implement `Future`. `Future` types can be used as `MoveFuture`s using one of two approaches:
- `Future` types that are `Unpin` can be converted to `MoveFuture` via an `into_move_future` method.
- Any `Future` contained in a `PinMut` or `PinBox` automatically implements `MoveFuture`.

This is accomplished using the following impls:

```rust
impl<'a, F: Future> MoveFuture for PinMut<'a, F> {
    type Output = F::Output;
    fn poll(&mut self) -> Self::Output {
        F::poll_pinned(self.reborrow())
    }
}

impl<F: Future> MoveFuture for PinBox<F> {
    type Output = F::Output;
    fn poll(&mut self) -> Self::Output {
        F::poll_pinned(self.as_pin_mut())
    }
}

impl<F: MoveFuture> Future for F {
    type Output = <F as MoveFuture>::Output;
    fn poll_pinned(mut self: PinMut<Self>) -> Self::Output {
        (*self).poll()
    }
}

// This wrapper is needed to avoid conflicting blanket implementations between
// `Future` and `MoveFuture`
struct MoveFutureWrap<T>(pub T);

trait IntoMoveFuture: Future + Unpin {
    fn into_move_future(self) -> MoveFutureWrap<Self>
        where Self: Sized
    {
        MoveFutureWrap(self)
    }
}

impl<T: Future + Unpin> IntoMoveFuture for T {}

impl<T: Future + Unpin> MoveFuture for MoveFutureWrap<T> {
    type Output = T::Output;
    fn poll(&mut self) -> Self::Output {
        PinMut::new(&mut self.0).poll_pinned()
    }
}
```

## `TryFuture`
[reference-tryfuture]: #reference-tryfuture

The definitions of `TryFuture` and `TryMoveFuture` make it simpler to bound child-futures
to only `Future`s with an output of `Result`:

```rust
pub trait TryFuture {
    type Item;
    type Error;
    fn try_poll_pinned(self: PinMut<Self>, cx: &mut task::Context)
        -> Poll<Result<Self::Item, Self::Error>>;
}

impl<F, T, E> TryFuture for F
    where F: Future<Output = Result<T, E>>
{
    type Item = T;
    type Error = E;

    fn try_poll_pinned(self: PinMut<Self>, cx: &mut task::Context) -> Poll<F::Output> {
        self.poll_pinned(cx)
    }
}

pub trait TryMoveFuture {
    type Item;
    type Error;
    fn try_poll(&mut self, cx: &mut task::Context)
        -> Poll<Result<Self::Item, Self::Error>>;
}

impl<F, T, E> TryMoveFuture for F
    where F: MoveFuture<Output = Result<T, E>>
{
    type Item = T;
    type Error = E;

    fn try_poll(&mut self, cx: &mut task::Context) -> Poll<Result<Self::Item, Self::Error>> {
        self.poll(cx)
    }
}

pub enum OrElse<FutOne, F, FutTwo> {
    First(FutOne, F),
    Second(FutTwo),
    Done,
}

impl<FutOne, F, FutTwo> Unpin for OrElse<FutOne, F, FutTwo> {}

// With `TryMoveFuture`
impl<FutOne, F, FutTwo> MoveFuture for OrElse
    where FutOne: TryMoveFuture,
          F: FnOnce(FutOne::Error) -> FutTwo,
          FutTwo: TryMoveFuture<Item = FutOne::Item, Error = FutOne::Error>,
{
    ...
}

// Without `TryMoveFuture`
impl<FutOne, F, FutTwo, T, E> MoveFuture for OrElse
    where FutOne: MoveFuture<Item = T, Error = E>,
          F: FnOnce(E) -> FutTwo,
          FutTwo: TryMoveFuture<Item = T, Error = E>,
{
    ...
}
```

Note that the implementation without `TryMoveFuture` requires type parameters for `T` and `E`,
which can be very unwieldy in certain situations. `TryFuture` and `TryMoveFuture` will be
defined in the `futures` crate.

One drawback of this specific definition is that `TryFuture` does not include a bound like
`Self: Future<Output = Result<Self as TryFuture>::Item, <Self as TryFuture>::Error>`, which
means that `TryFuture` cannot be used as a `Future` directly, and is only practically usable
in functions that directly `poll` the `TryFuture`. This is an unfortunate but temporary
limitation: the trait system is not currently capable of understanding the above constraint,
but the constraint is expressible in a system called "Chalk" that is forming the basis for
an ongoing trait system revamp in the compiler. This should allow `TryFuture` to eventually
be migrated to the more correct version-- keeping `TryFuture` in the `futures` crate makes
it possible to make breaking changes like this.

## Details for `no_std` compatibility

The APIs proposed above are almost entirely compatible with `core`, except for a
couple of constructors that require `std` objects:

- Constructing a `Waker` from an `Arc<T>: Wake`
- Constructing a `TaskObj` from a future

These both have a similar shape: we have a concrete but opaque type (`Waker`,
`TaskObj`) that represents a trait object, but does *not* force a particular
*representation* for the trait object. In `std` environments, you can largely
gloss over this point and just use `Arc` or `Box` respectively. But internally,
the `Waker` and `TaskObj` types are more abstract.

We'll look at the `Waker` case in detail. The idea is to provide an `UnsafeWake`
trait which represents "an arbitrary `Wake`-like trait object":

```rust
/// An unsafe trait for implementing custom memory management for a
/// `Waker`.
///
/// A `Waker` conceptually is a cloneable trait object for `Wake`, and is
/// most often essentially just `Arc<T>: Wake`. However, in some contexts
/// (particularly `no_std`), it's desirable to avoid `Arc` in favor of some
/// custom memory management strategy. This trait is designed to allow for such
/// customization.
///
/// A default implementation of the `UnsafeWake` trait is provided for the
/// `Arc` type in the standard library.
pub unsafe trait UnsafeWake {
    /// Creates a new `Waker` from this instance of `UnsafeWake`.
    ///
    /// This function will create a new uniquely owned handle that under the
    /// hood references the same notification instance. In other words calls
    /// to `wake` on the returned handle should be equivalent to calls to
    /// `wake` on this handle.
    ///
    /// # Unsafety
    ///
    /// This function is unsafe to call because it's asserting the `UnsafeWake`
    /// value is in a consistent state, i.e. hasn't been dropped.
    unsafe fn clone_raw(self: *mut Self) -> Waker;

    /// Drops this instance of `UnsafeWake`, deallocating resources
    /// associated with it.
    ///
    /// # Unsafety
    ///
    /// This function is unsafe to call because it's asserting the `UnsafeWake`
    /// value is in a consistent state, i.e. hasn't been dropped
    unsafe fn drop_raw(self: *mut Self);

    /// Indicates that the associated task is ready to make progress and should
    /// be `poll`ed.
    ///
    /// Executors generally maintain a queue of "ready" tasks; `wake` should place
    /// the associated task onto this queue.
    ///
    /// # Panics
    ///
    /// Implementations should avoid panicking, but clients should also be prepared
    /// for panics.
    ///
    /// # Unsafety
    ///
    /// This function is unsafe to call because it's asserting the `UnsafeWake`
    /// value is in a consistent state, i.e. hasn't been dropped
    unsafe fn wake(self: *mut self);
}
```

We then provide the following constructor for `Waker`:

```rust
impl Waker {
    pub unsafe fn new(inner: *const dyn UnsafeWake) -> Waker;
}
```

and a `From<Arc<T>>` (where `Arc<T>: Wake`) impl that uses it.

## Task-local storage

This RFC does not propose any implicit, built-in task-local storage. (Explicit
storage is always possible).

Task-local storage is implementable on top of the proposed APIs by wrapping a
task in a *scoped* use of *thread*-local storage. When polling the task, a
thread-local value is established and hence usable implicitly within the call
chain. But when returning -- which also happens when the task is blocked -- the
thread-local is moved back out and stored with the task.

In the future, we anticipate adding "spawn hooks" for the `Context::spawn`
method, essentially allowing you to guarantee that tasks spawned within some
scope are wrapped in some way. That's a separately useful feature, but it can in
particular be used to implement inheritance of task-local data.

It may be that eventually we do want to build in some task-local data scheme, but:

- The no_std story is unclear.
- There are a lot of possible designs around things like typemaps and
  inheritance, and so it seems best for this work to begin in the ecosystem
  first.



# Drawbacks
[drawbacks]: #drawbacks

This RFC is one of the most substantial additions to `std` proposed since
1.0. It commits us to including a particular task and polling model in the
standard library. The stakes are high.

However, as argued in the stabilization section above, the meat of the proposal
has at this point already been thoroughly vetted; the core ideas go back about
two years at this point. It's possible to carve an extremely minimal path to
stabilization that essentially sticks to these already-proven ideas. Likewise,
async/await support (via generators) has already existing on the nightly channel
for quite a long time.

So far we've been able to push the task/polling model into virtually every niche
Rust wishes to occupy, and the main downside has been, in essence, the lack of
async/await syntax (and
the
[borrowing it supports](http://aturon.github.io/2018/04/24/async-borrowing/)).

# Rationale and alternatives
[alternatives]: #alternatives

This RFC does not attempt to provide a complete introduction to the task model
that originated with the futures crate. A fuller account of the design rationale
and alternatives can be found in the following two blog posts:

- [Zero-cost futures in Rust](http://aturon.github.io/2016/08/11/futures/)
- [Designing futures for Rust](http://aturon.github.io/2016/09/07/futures-design/)

To summarize, the main alternative model for futures is a callback-based approach,
which was attempted for several months before the current approach was discovered.
In our experience, the callback approach suffered from several drawbacks in Rust:

- It forced allocation almost everywhere, and hence was not compatible with no_std.
- It made cancellation *extremely* difficult to get right, whereas with the
  proposed model it's just "drop".
- Subjectively, the combinator code was quite hairy, while with the task-based model
  things fell into place quickly and easily.

Some additional context and rationale is available in the [companion RFC].

# Prior art
[prior-art]: #prior-art

There is substantial prior art both with async/await notation and with futures
(aka promises) as a basis. The proposed futures API was influenced by Scala's
futures in particular, and is broadly similar to APIs in a variety of other
languages (in terms of the adapters provided).

What's more unique about the model in this RFC is the use of tasks, rather than
callbacks. The RFC author is not aware of other *futures* libraries using this
technique, but it is a fairly well-known technique more generally in functional
programming. For a recent example,
see
[this paper](https://www.microsoft.com/en-us/research/wp-content/uploads/2011/01/monad-par.pdf) on
parallelism in Haskell. What seems to be perhaps new with this RFC is the idea
of melding the "trampoline" technique with an explicit, open-ended task/wakeup
model.

# Unresolved questions
[unresolved]: #unresolved-questions

- Optimize the story around `TryFuture`, and figure out how soon we can get compiler
  support for the ideal trait definition that allows both direct polling and
  use with `async`/`await`.
