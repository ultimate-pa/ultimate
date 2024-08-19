
## Open issues
  * ``broken-patterns.txt`` describes issues with existing patterns that can be parsed and interpreted, but where the interpretation is misleading. 
  * ``not-implemented/`` contains patterns which are simply not implemented (i.e., there is no countertrace) 
  * ``scope-issues/`` contains patterns that can never be part of an rt-consistency because the system just avoids entering the scope altogether. 

  	Example:
  	req1: Before "var1" It is always the case that once "var4" becomes satisfied, it holds for at least "10" time units.
	req2: Before "var1" It is always the case that "!var4" holds at least every "5" time units.

	The above requirements are rt-inconsistent under the assumption that the scope is not left, i.e. "!var1" holds. This assumption however is not represented in the rt-consistency check. The scope can hence be left and the pair of requirements can never be part of an rt-inconsistncy. 
  * ``toggle-issues/`` contains different issues with the toggle pattern (may be already fixed as soon as ``broken_patterns.txt`` is fixed)
* ``other/`` contains testcases that fail to prove some of the properties, e.g., due to timeout etc.
