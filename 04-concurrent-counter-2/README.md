# Concurrent counter (2)

Write a TLA+ spec for a shared counter.
The counter is initially 0, and 2 threads **non-atomically** increase the value (first read, then write).

- Check that value of the counter is always between 0 and 2.
- Find a behavior where the final counter value is 1.
- Check that final counter value can never be 0 (assuming the threads can make progress).
