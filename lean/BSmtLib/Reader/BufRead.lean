module

public import Std.Data.ByteSlice

public section

/- LEAN: not in Rust, whose lexer and reader read from `std::io::BufRead`. Its stand-in is in the
namespace of the reader, which reads from it, but in a module of its own, which the lexer imports
too, as the reader's module imports the lexer's. -/

namespace BSmtLib.Reader

/- LEAN: Rust's `std::io::BufRead`, which Lean's standard library does not have. Methods taking
`&mut self` return the updated reader; an I/O error is returned rather than thrown, as Rust
returns it. -/
/--
Source of bytes read through a buffer, in the monad `n`.

`fillBuf` returns the bytes buffered and not consumed yet, filling the buffer from the source
first if none are left; it returns no bytes at the end of the input. `consume` marks the given
number of bytes at the start of the buffer as consumed, so that `fillBuf` does not return them
again.
-/
class BufRead (B : Type) (n : Type → Type) where
  /--
  Returns the bytes buffered and not consumed yet, filling the buffer from the source if none
  are left. No bytes are returned at the end of the input.
  -/
  fillBuf : B → n (Except IO.Error (ByteSlice × B))
  /--
  Marks the first `amount` bytes of the buffer as consumed.

  The amount must not be more than `fillBuf` returned last.
  -/
  consume : B → Nat → B

/- LEAN: Rust's `impl BufRead for &[u8]`. -/
instance {n : Type → Type} [Monad n] : BufRead ByteSlice n where
  fillBuf slice := pure (.ok (slice, slice))
  consume slice amount := slice.slice amount

/- LEAN: Rust's `std::io::BufReader`, over a stream, which Lean's file handles and in-memory
buffers both give (`IO.FS.Stream.ofHandle`, `IO.FS.Stream.ofBuffer`). -/
/-- Stream read through a buffer of a fixed capacity. -/
structure BufReader where
  private mk ::
  private stream : IO.FS.Stream
  private capacity : Nat
  /-- The bytes read from the stream last. -/
  private buffer : ByteArray
  /-- The number of bytes of the buffer consumed. -/
  private position : Nat

/- LEAN: Rust's `BufReader::with_capacity`. -/
/-- Creates a reader of `stream` through a buffer of `capacity` bytes. -/
def BufReader.new (stream : IO.FS.Stream) (capacity : Nat) : BufReader :=
  { stream, capacity, buffer := ByteArray.empty, position := 0 }

@[no_expose] instance {n : Type → Type} [Monad n] [MonadLiftT IO n] : BufRead BufReader n where
  fillBuf self := do
    if self.position < self.buffer.size then
      return .ok (self.buffer.toByteSlice self.position, self)
    -- the buffer has been consumed, fill it from the stream
    let read : IO (Except IO.Error ByteArray) := (self.stream.read self.capacity.toUSize).toBaseIO
    match ← read with
    | .ok buffer => return .ok (buffer.toByteSlice, { self with buffer, position := 0 })
    | .error err => return .error err
  consume self amount := { self with position := self.position + amount }

end BSmtLib.Reader
