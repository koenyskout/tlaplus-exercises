# Concurrent counter (1)

Write a TLA+ spec for a shared counter.
The counter is initially 0, and 2 threads **atomically** increase its value.

Check that the counter value is always between 0 and 2, and that it eventually becomes 2.

