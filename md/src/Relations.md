<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/Relations.lean'>Code</a> for this chapter</span>
 # Relations

As described previously, a relation is a propositionally valued predicate of two arguments. Generally speaking, that is about all you can say about predicates. However, when we restrict our attention to predicates having specific properties, we can say much more.

In this chapter we will build up some of the theory behind relations and give several examples of each type of relation.

Note that Mathlib has many definitions involved relations. In particular, `Rel` is the general type of relations. We will not use that infrastructure in this chapter, as our goal is to build up the theory from scratch for the purposes of understanding it better, which in turn should make Mathlib more comprehensible.

## Definitions

First, we define a general type for relations: 

<div style='height=50px'>&nbsp;</div><hr>
Copyright © Eric Klavins, 2025-Present
