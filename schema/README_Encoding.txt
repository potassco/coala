
The encodings in the encodings/ folder are
written to fit the BC paper.

For a given horizon k, the fixed encoding
contains an initial step 0 and all path starting from it with k transitions.

For the initial step,
a choice creates all possible states.

Effects of static laws hold if all conditions of the if part are fulfilled in the same step
and the ifcons part can be assumed in the current step.

Effects of dynamic laws hold if the fluent conditions and actions 
of the after part are fulfilled in the previous step
and the ifcons part can be assumed in the current step.


