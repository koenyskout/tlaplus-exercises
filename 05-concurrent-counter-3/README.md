# Concurrent counter (3)

Generalize the [previous model](../04-concurrent-counter-2/) to N threads, where N is a parameter of the model.

_Hint: use functions to represent state_

- Check that value of the counter is always between 0 and N.
- Find a behavior where the final counter value is 1.
- Check that final counter value can never be 0 (assuming the threads can make progress).
