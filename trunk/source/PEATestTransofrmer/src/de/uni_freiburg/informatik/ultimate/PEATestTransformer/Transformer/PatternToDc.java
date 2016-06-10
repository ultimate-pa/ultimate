package de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer;

import pea.CDD;
import pea.CounterTrace;
import pea.PhaseEventAutomata;
import srParse.srParseScopeAfter;
import srParse.srParseScopeAfterUntil;
import srParse.srParseScopeBefore;
import srParse.srParseScopeBetween;
import srParse.srParseScopeGlob;
import srParse.pattern.BndResponsePattern;
import srParse.pattern.InstAbsPattern;
import srParse.pattern.InvariantPattern;
import srParse.pattern.PatternType;
import srParse.pattern.UniversalityPattern;



public class PatternToDc {
	
	/*
	 * Translates a pattern type into a Counter trace DC Formula
	 */
	public CounterTrace translate(PatternType pattern, CDD p, CDD q, CDD r, CDD s, int t){
		//switch pattern x
		/* scope.contains("Globally")	-> srParseScopeGlobally
		 * scope.contains("Before")		-> srParseScopeBefore
		 * scope.contains("until")		-> srParseScopeAfterUntil
		 * scope.contains("After")		-> srParseScopeAfter
		 * scope.contains("Between")	-> srParseScopeBetween
		 */
		if(pattern instanceof InvariantPattern){
			// ... it is always the case that if s holds then p holds.
			if(pattern.getScope().getClass() == srParseScopeGlob.class){	
				return this.GlobalInvariantPattern(pattern, p, q, r, s);			//test [yes]
			} else if (pattern.getScope().getClass() == srParseScopeBefore.class){	
				return this.BeforeInvariantPattern(pattern, p, q, r, s);			//test [yes]
			} else if (pattern.getScope().getClass() == srParseScopeAfterUntil.class){	
				return this.AfterUntilInvariantPattern(pattern, p, q, r, s);		//test [yes]
			} else if (pattern.getScope().getClass() == srParseScopeAfter.class){
				return this.AfterInvariantPattern(pattern, p, q, r, s);				//test [yes]
			} else if (pattern.getScope().getClass() == srParseScopeBetween.class){	
				return this.BetweenInvariantPattern(pattern, p, q, r, s);			//test []
			} else {throw new UnsupportedOperationException();}
			
		} else if (pattern instanceof InstAbsPattern){
			// ... it is never the case that s holds.
			if(pattern.getScope().getClass() == srParseScopeGlob.class){	
				return this.GlobalInstAbsPattern(pattern, p, q, r, s);				//test [yes]
			} else if (pattern.getScope().getClass() == srParseScopeBefore.class){	
				return this.BeforeInstAbsPattern(pattern, p, q, r, s);				//test [yes]
			} else if (pattern.getScope().getClass() == srParseScopeAfterUntil.class){	
				return this.AfterUntilInstAbsPattern(pattern, p, q, r, s);			//test [yes]
			} else if (pattern.getScope().getClass() == srParseScopeAfter.class){
				return this.AfterInstAbsPattern(pattern, p, q, r, s);				//test [yes]
			} else if (pattern.getScope().getClass() == srParseScopeBetween.class){	
				return this.BetweenInstAbsPattern(pattern, p, q, r, s);				//test [yes]
			} else {throw new UnsupportedOperationException();}
			
		} else if (pattern instanceof UniversalityPattern){
			// ... it is always the case that s holds.
			if(pattern.getScope().getClass() == srParseScopeGlob.class){	
				return this.GlobalUniversality(pattern, p, q, r, s);				//test []
			} else if (pattern.getScope().getClass() == srParseScopeBefore.class){	
				return this.BeforeUniversality(pattern, p, q, r, s);				//test []
			} else if (pattern.getScope().getClass() == srParseScopeAfterUntil.class){	
				return this.AfterUntilUniversality(pattern, p, q, r, s);			//test []
			} else if (pattern.getScope().getClass() == srParseScopeAfter.class){
				return this.AfterUniversality(pattern, p, q, r, s);					//test []
			} else if (pattern.getScope().getClass() == srParseScopeBetween.class){	
				return this.BetweenUniversality(pattern, p, q, r, s);				//test []
			} else {throw new UnsupportedOperationException();}
	
		} else if (pattern instanceof BndResponsePattern){
			// ... it is never the case that s holds.
			if(pattern.getScope().getClass() == srParseScopeGlob.class){	 
				return this.GlobalBndResponsePattern(pattern, p, q, r, s, t);			//test []
			} else if (pattern.getScope().getClass() == srParseScopeBefore.class){	
				//return this.BeforeBndResponsPattern(pattern, p, q, r, s);				//test []
				return null;
			} else if (pattern.getScope().getClass() == srParseScopeAfterUntil.class){	
				//return this.AfterUntilBndResponsPattern(pattern, p, q, r, s);			//test []
				return null;
			} else if (pattern.getScope().getClass() == srParseScopeAfter.class){
				//return this.AfterBndResponsPattern(pattern, p, q, r, s);				//test []
				return null;
			} else if (pattern.getScope().getClass() == srParseScopeBetween.class){	
				//return this.BetweenBndResponsPattern(pattern, p, q, r, s);				//test []
				return null;
			} else {throw new UnsupportedOperationException();}
			
		} else {
			throw new UnsupportedOperationException("Pattern not implemented");
		}
	}
	
	protected CounterTrace GlobalBndResponsePattern(PatternType pattern, CDD p, CDD q, CDD r, CDD s, int t){ 
		return new CounterTrace(new CounterTrace.DCPhase[] {
			    new CounterTrace.DCPhase(),
			    new CounterTrace.DCPhase(p.and(s.negate())),
			    new CounterTrace.DCPhase(s.negate(), CounterTrace.BOUND_GREATER, t),
			    new CounterTrace.DCPhase()
			});
	}
	
	//Universality Pattern
	protected CounterTrace GlobalUniversality(PatternType pattern, CDD p, CDD q, CDD r, CDD s){ 
		return new CounterTrace(new CounterTrace.DCPhase[] {
			    new CounterTrace.DCPhase(),
			    new CounterTrace.DCPhase(p.negate()), 
			    new CounterTrace.DCPhase()
			});
	}

	protected CounterTrace BeforeUniversality(PatternType pattern, CDD p, CDD q, CDD r, CDD s){ 
		return new CounterTrace(new CounterTrace.DCPhase[] {
			    new CounterTrace.DCPhase(q.negate()),
			    new CounterTrace.DCPhase(q.negate().and(p)),
			    new CounterTrace.DCPhase()
			});
	}

	protected CounterTrace AfterUniversality(PatternType pattern, CDD p, CDD q, CDD r, CDD s){ 
		return new CounterTrace(new CounterTrace.DCPhase[] {
				new CounterTrace.DCPhase(),
			    new CounterTrace.DCPhase(q),
			    new CounterTrace.DCPhase(),
			    new CounterTrace.DCPhase(p.and(s.negate())),
			    new CounterTrace.DCPhase()
			});
	}

	protected CounterTrace BetweenUniversality(PatternType pattern, CDD p, CDD q, CDD r, CDD s){ 
		return new CounterTrace(new CounterTrace.DCPhase[] {
				new CounterTrace.DCPhase(),
			    new CounterTrace.DCPhase(q.and(r.negate())),
			    new CounterTrace.DCPhase(r.negate()),
			    new CounterTrace.DCPhase(r.negate().and(p.negate())),
			    new CounterTrace.DCPhase(r.negate()),
			    new CounterTrace.DCPhase(r),
			    new CounterTrace.DCPhase()
			});
	}

	protected CounterTrace AfterUntilUniversality(PatternType pattern, CDD p, CDD q, CDD r, CDD s){ 
		return new CounterTrace(new CounterTrace.DCPhase[] {
				new CounterTrace.DCPhase(),
			    new CounterTrace.DCPhase(r.negate().and(q)),
			    new CounterTrace.DCPhase(r.negate()),
			    new CounterTrace.DCPhase(r.negate().and(p.negate())),
			    new CounterTrace.DCPhase()
			});
	}

	
	//AbsencePattern (InstAbsPattern)
	protected CounterTrace GlobalInstAbsPattern(PatternType pattern, CDD p, CDD q, CDD r, CDD s){ 
		return new CounterTrace(new CounterTrace.DCPhase[] {
			    new CounterTrace.DCPhase(),
			    new CounterTrace.DCPhase(p),
			    new CounterTrace.DCPhase()
			});
	}
	
	protected CounterTrace BeforeInstAbsPattern(PatternType pattern, CDD p, CDD q, CDD r, CDD s){ 
		return new CounterTrace(new CounterTrace.DCPhase[] {
    		    new CounterTrace.DCPhase(r.negate()),
    		    new CounterTrace.DCPhase(p.and(r.negate())),
    		    new CounterTrace.DCPhase(r.negate()),
    		    new CounterTrace.DCPhase(r),
    		    new CounterTrace.DCPhase()
    		 });    	
	}
	
	protected CounterTrace AfterUntilInstAbsPattern(PatternType pattern, CDD p, CDD q, CDD r, CDD s){ 
		return new CounterTrace(new CounterTrace.DCPhase[] {
	               	    new CounterTrace.DCPhase(),
	               	    new CounterTrace.DCPhase(q.and(r.negate())),
	               	    new CounterTrace.DCPhase(r.negate()),
	               	    new CounterTrace.DCPhase(p.and(r.negate())),
	               	    new CounterTrace.DCPhase()
	               	});   
	}

	protected CounterTrace AfterInstAbsPattern(PatternType pattern, CDD p, CDD q, CDD r, CDD s){ 
		return new CounterTrace(new CounterTrace.DCPhase[] {
	    	    new CounterTrace.DCPhase(),
	    	    new CounterTrace.DCPhase(q),
	    	    new CounterTrace.DCPhase(),
	    	    new CounterTrace.DCPhase(p),
	    	    new CounterTrace.DCPhase()
	    	});    	
	}
	
	protected CounterTrace BetweenInstAbsPattern(PatternType pattern, CDD p, CDD q, CDD r, CDD s){ 
		return new CounterTrace(new CounterTrace.DCPhase[] {
    	  	    new CounterTrace.DCPhase(),
    	   	    new CounterTrace.DCPhase(q.and(r.negate())),
    	   	    new CounterTrace.DCPhase(r.negate()),
    	   	    new CounterTrace.DCPhase(p.and(r.negate())),
    	   	    new CounterTrace.DCPhase(r.negate()),
    	   	    new CounterTrace.DCPhase(r),
    	  	  new CounterTrace.DCPhase()
    	   	});    	
	}
	
	//InvariantPattern
	// Is absence pattern with absencePattern(P.and(S.negate()),Q,R, scope);
	/* public PhaseEventAutomata invariantPattern(CDD P, CDD Q, CDD R, CDD S, String scope) {
    	 ctA = absencePattern(P.and(S.negate()),Q,R, scope);
    	 */
	protected CounterTrace GlobalInvariantPattern(PatternType pattern, CDD p, CDD q, CDD r, CDD s){ 
		return new CounterTrace(new CounterTrace.DCPhase[] {
				    new CounterTrace.DCPhase(),
				    new CounterTrace.DCPhase(p.and(s.negate())),
				    new CounterTrace.DCPhase()
				});
	}
	
	protected CounterTrace BeforeInvariantPattern(PatternType pattern, CDD p, CDD q, CDD r, CDD s){ 
		//Before R it is always the case that if p holds then s holds as well.
		return new CounterTrace(new CounterTrace.DCPhase[] {
    		    new CounterTrace.DCPhase(r.negate()),
    		    new CounterTrace.DCPhase(p.and(s.negate()).and(r.negate())),
    		    new CounterTrace.DCPhase(r.negate()),
    		    new CounterTrace.DCPhase(r),
    		    new CounterTrace.DCPhase()
    		 });    	
	}
	
	protected CounterTrace AfterUntilInvariantPattern(PatternType pattern, CDD p, CDD q, CDD r, CDD s){ 
		return new CounterTrace(new CounterTrace.DCPhase[] {
           	    new CounterTrace.DCPhase(),
           	    new CounterTrace.DCPhase(q.and(r.negate())),
           	    new CounterTrace.DCPhase(r.negate()),
           	    new CounterTrace.DCPhase(p.and(r.negate())),
           	    new CounterTrace.DCPhase()
           	});    	
	}

	protected CounterTrace AfterInvariantPattern(PatternType pattern, CDD p, CDD q, CDD r, CDD s){ 
		return new CounterTrace(new CounterTrace.DCPhase[] {
	    	    new CounterTrace.DCPhase(),
	    	    new CounterTrace.DCPhase(q),
	    	    new CounterTrace.DCPhase(),
	    	    new CounterTrace.DCPhase(p.and(s.negate())),
	    	    new CounterTrace.DCPhase()
	    	});    	
	}
	
	protected CounterTrace BetweenInvariantPattern(PatternType pattern, CDD p, CDD q, CDD r, CDD s){ 
		return new CounterTrace(new CounterTrace.DCPhase[] {
    	  	    new CounterTrace.DCPhase(),
    	   	    new CounterTrace.DCPhase(q.and(r.negate())),
    	   	    new CounterTrace.DCPhase(r.negate()),
    	   	    new CounterTrace.DCPhase(p.and(r.negate())),
    	   	    new CounterTrace.DCPhase(r.negate()),
    	   	    new CounterTrace.DCPhase(r),
    	  	  new CounterTrace.DCPhase()
    	   	});    	
	}

}
