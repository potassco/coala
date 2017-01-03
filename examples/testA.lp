action(a).
fluent(f).
domain(f,true). domain(f,false). 


dynamic_law(law(1)).
head(law(1),val(f,true)).
after(law(1),a).

static_law(law(3)).
head(law(3),val(f,false)).
ifcons(law(3),val(f,false)).


#show holds/2.
#show occurs/2.
