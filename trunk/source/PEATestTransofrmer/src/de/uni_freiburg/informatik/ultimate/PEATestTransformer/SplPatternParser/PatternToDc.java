package de.uni_freiburg.informatik.ultimate.PEATestTransformer.SplPatternParser;

import de.uni_freiburg.informatik.ultimate.PEATestTransformer.SystemInformation;
import pea.CDD;
import pea.CounterTrace;
import pea.PhaseEventAutomata;
import srParse.pattern.ResponsePattern;
import srParse.srParseScopeAfter;
import srParse.srParseScopeAfterUntil;
import srParse.srParseScopeBefore;
import srParse.srParseScopeBetween;
import srParse.srParseScopeGlob;
import srParse.pattern.BndExistencePattern;
import srParse.pattern.BndInvariancePattern;
import srParse.pattern.BndResponsePattern;
import srParse.pattern.InitializationPattern;
import srParse.pattern.InstAbsPattern;
import srParse.pattern.InvariantPattern;
import srParse.pattern.PatternType;
import srParse.pattern.UniversalityPattern;



public class PatternToDc {
	
	
	public CounterTrace translate(PatternType pattern){
		//get CDDs
		 
		CDD q = pattern.getScope().getCdd1(); 
		CDD r = pattern.getScope().getCdd2();
		CDD s = null;
		CDD p = null;
		if (pattern.getCdds().size() > 1)
			{
				s =  pattern.getCdds().get(0);
				p = pattern.getCdds().get(1);
			} else {
				p = pattern.getCdds().get(0);
			}
		int t = pattern.getDuration();
		return this.translate(pattern, q, r, p, s, t);
	} 
	/*
	 * Translates a pattern type into a Counter trace DC Formula
	 */
	public CounterTrace translate(PatternType pattern, CDD q, CDD r, CDD p, CDD s, int t){
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
				return this.GlobalInvariantPattern(pattern, q, r, p, s);			//test []
			} else if (pattern.getScope().getClass() == srParseScopeBefore.class){	
				return this.BeforeInvariantPattern(pattern, q, r, p, s);			//test []
			} else if (pattern.getScope().getClass() == srParseScopeAfterUntil.class){	
				return this.AfterUntilInvariantPattern(pattern, q, r, p, s);		//test [manual]
			} else if (pattern.getScope().getClass() == srParseScopeAfter.class){
				return this.AfterInvariantPattern(pattern, q, r, p, s);				//test []
			} else if (pattern.getScope().getClass() == srParseScopeBetween.class){	
				return this.BetweenInvariantPattern(pattern, q, r, p, s);			//test []
			} else {throw new UnsupportedOperationException();}
		} else if (pattern instanceof InstAbsPattern){
			// ... it is never the case that s holds.
			if(pattern.getScope().getClass() == srParseScopeGlob.class){	
				return this.GlobalInstAbsPattern(pattern, q, r, p, s);				//test []
			} else if (pattern.getScope().getClass() == srParseScopeBefore.class){	
				return this.BeforeInstAbsPattern(pattern, q, r, p, s);				//test []
			} else if (pattern.getScope().getClass() == srParseScopeAfterUntil.class){	
				return this.AfterUntilInstAbsPattern(pattern, q, r, p, s);			//test []
			} else if (pattern.getScope().getClass() == srParseScopeAfter.class){
				return this.AfterInstAbsPattern(pattern, q, r, p, s);				//test []
			} else if (pattern.getScope().getClass() == srParseScopeBetween.class){	
				return this.BetweenInstAbsPattern(pattern, q, r, p, s);				//test []
			} else {throw new UnsupportedOperationException();}
			
		} else if (pattern instanceof UniversalityPattern){
			// ... it is always the case that s holds.
			if(pattern.getScope().getClass() == srParseScopeGlob.class){	
				return this.GlobalUniversality(pattern, q, r, p, s);				//test []
			} else if (pattern.getScope().getClass() == srParseScopeBefore.class){	
				return this.BeforeUniversality(pattern, q, r, p, s);				//test []
			} else if (pattern.getScope().getClass() == srParseScopeAfterUntil.class){	
				return this.AfterUntilUniversality(pattern, q, r, p, s);			//test [manual]
			} else if (pattern.getScope().getClass() == srParseScopeAfter.class){
				return this.AfterUniversality(pattern, q, r, p, s);					//test [manual]
			} else if (pattern.getScope().getClass() == srParseScopeBetween.class){	
				return this.BetweenUniversality(pattern, q, r, p, s);				//test []
			} else {
				throw new UnsupportedOperationException();}
			
		} else if (pattern instanceof BndInvariancePattern){
			// ... it is always the case that if p holds after at most c time units.
			if(pattern.getScope().getClass() == srParseScopeGlob.class){	 
				return this.GlobalBndInvariancePattern(pattern, q, r, p, s, t);			//test [used]
			} else {
				throw new UnsupportedOperationException();
			}
		} else if (pattern instanceof BndResponsePattern){
			// ... it is always the case that if p holds after at most c time units.
			if(pattern.getScope().getClass() == srParseScopeGlob.class){	 
				return this.GlobalBndResponsePattern(pattern, q, r, p, s, t);			//test [used]
			} else if(pattern.getScope().getClass() == srParseScopeAfterUntil.class){	 
				return this.AfterUnitlBndResponsePattern(pattern, q, r, p, s, t);			//test []
			} else {
				throw new UnsupportedOperationException();
			}
		} else if (pattern instanceof BndExistencePattern){
			// ... it is always the case that if p holds after at most c time units.
			if(pattern.getScope().getClass() == srParseScopeBefore.class){	 
				return this.GlobalBndExistence(pattern, q, r, p, s, t);			//test []
			} else if(pattern.getScope().getClass() == srParseScopeAfter.class){	 
				return this.AfterBndExistence(pattern, q, r, p, s, t);			//test []
			} else if(pattern.getScope().getClass() == srParseScopeAfterUntil.class){	 
				return this.AfterUntilBndExistence(pattern, q, r, p, s, t);			//test [!!! FAIL wegen phase 4]
			} else {
				throw new UnsupportedOperationException();
			}
		} else {
			throw new UnsupportedOperationException("Pattern not implemented");
		}
	}
	
	protected CounterTrace AfterBndExistence(PatternType pattern, CDD q, CDD r, CDD p, CDD s, int t){
		pattern.setEffect(p);
		return new CounterTrace(new CounterTrace.DCPhase[] {
			    new CounterTrace.DCPhase(),
			    new CounterTrace.DCPhase(q),
			    new CounterTrace.DCPhase(),
			    new CounterTrace.DCPhase(p),
			    new CounterTrace.DCPhase(p.negate()),
			    new CounterTrace.DCPhase(p),
			    new CounterTrace.DCPhase(p.negate()),
			    new CounterTrace.DCPhase(p),
			    new CounterTrace.DCPhase(),
			});
	}
	
	protected CounterTrace AfterUntilBndExistence(PatternType pattern, CDD q, CDD r, CDD p, CDD s, int t){
		pattern.setEffect(p);
		return new CounterTrace(new CounterTrace.DCPhase[] {
			    new CounterTrace.DCPhase(),
			    new CounterTrace.DCPhase(q.and(r.negate())),
			    new CounterTrace.DCPhase(r.negate()),
			    new CounterTrace.DCPhase(p.and(r.negate())),
			    new CounterTrace.DCPhase(p.negate().and(r.negate())),
			    new CounterTrace.DCPhase(p.and(r.negate())),
			    new CounterTrace.DCPhase(p.negate().and(r.negate())),
			    new CounterTrace.DCPhase(p.and(r.negate())),
			    new CounterTrace.DCPhase(r.negate()),
			    new CounterTrace.DCPhase(),
			});
	}
	
	protected CounterTrace AfterUnitlBndResponsePattern(PatternType pattern, CDD q, CDD r, CDD p, CDD s, int t){
		pattern.setEffect(s);
		return new CounterTrace(new CounterTrace.DCPhase[] {
			    new CounterTrace.DCPhase(),
			    new CounterTrace.DCPhase(q),
			    new CounterTrace.DCPhase(),
			    new CounterTrace.DCPhase(p.and(s.negate())),
			    new CounterTrace.DCPhase(s.negate(), CounterTrace.BOUND_GREATER, t),
			    new CounterTrace.DCPhase()
			});
	}
	
	protected CounterTrace GlobalBndExistence(PatternType pattern, CDD q, CDD r, CDD p, CDD s, int t){
		pattern.setEffect(p);
		return new CounterTrace(new CounterTrace.DCPhase[] {
			    new CounterTrace.DCPhase(),
			    new CounterTrace.DCPhase(p),
			    new CounterTrace.DCPhase(p.negate()),
			    new CounterTrace.DCPhase(p),
			    new CounterTrace.DCPhase(p.negate()),
			    new CounterTrace.DCPhase(p),
			    new CounterTrace.DCPhase()
			});
	}
	
		protected CounterTrace GlobalBndInvariancePattern(PatternType pattern, CDD q, CDD r, CDD p, CDD s, int t){
		pattern.setEffect(s);
		return new CounterTrace(new CounterTrace.DCPhase[] {
			    new CounterTrace.DCPhase(),
			    new CounterTrace.DCPhase(p),
			    new CounterTrace.DCPhase(CounterTrace.BOUND_LESS, t),
			    new CounterTrace.DCPhase(s.negate()),
			    new CounterTrace.DCPhase()
			});
	}
	
	protected CounterTrace GlobalBndResponsePattern(PatternType pattern, CDD q, CDD r, CDD p, CDD s, int t){
		pattern.setEffect(s);
		return new CounterTrace(new CounterTrace.DCPhase[] {
			    new CounterTrace.DCPhase(),
			    new CounterTrace.DCPhase(p.and(s.negate())),
			    new CounterTrace.DCPhase(s.negate(), CounterTrace.BOUND_GREATER, t),
			    new CounterTrace.DCPhase()
			});
	}
	
	//Universality Pattern
	protected CounterTrace GlobalUniversality(PatternType pattern, CDD q, CDD r, CDD p, CDD s){ 
		pattern.setEffect(p);
		return new CounterTrace(new CounterTrace.DCPhase[] {
			    new CounterTrace.DCPhase(),
			    new CounterTrace.DCPhase(p.negate()), 
			    new CounterTrace.DCPhase()
			});
	}

	protected CounterTrace BeforeUniversality(PatternType pattern, CDD q, CDD r, CDD p, CDD s){ 
		return new CounterTrace(new CounterTrace.DCPhase[] {
			    new CounterTrace.DCPhase(q.negate()),
			    new CounterTrace.DCPhase(q.negate().and(p)),
			    new CounterTrace.DCPhase()
			});
	}

	protected CounterTrace AfterUniversality(PatternType pattern, CDD q, CDD r, CDD p, CDD s){ 
		pattern.setEffect(p);
		return new CounterTrace(new CounterTrace.DCPhase[] {
				new CounterTrace.DCPhase(),
			    new CounterTrace.DCPhase(q),
			    new CounterTrace.DCPhase(),
			    new CounterTrace.DCPhase(p.negate()),
			    new CounterTrace.DCPhase()
			});
	}

	protected CounterTrace BetweenUniversality(PatternType pattern, CDD q, CDD r, CDD p, CDD s){ 
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

	protected CounterTrace AfterUntilUniversality(PatternType pattern, CDD q, CDD r, CDD p, CDD s){ 
		pattern.setEffect(p);
		return new CounterTrace(new CounterTrace.DCPhase[] {
				new CounterTrace.DCPhase(),
			    new CounterTrace.DCPhase(r.negate().and(q)),
			    new CounterTrace.DCPhase(r.negate()),
			    new CounterTrace.DCPhase(r.negate().and(p.negate())),
			    new CounterTrace.DCPhase()
			});
	}

	
	//AbsencePattern (InstAbsPattern)
	protected CounterTrace GlobalInstAbsPattern(PatternType pattern, CDD q, CDD r, CDD p, CDD s){ 
		pattern.setEffect(p);
		return new CounterTrace(new CounterTrace.DCPhase[] {
			    new CounterTrace.DCPhase(),
			    new CounterTrace.DCPhase(p),
			    new CounterTrace.DCPhase()
			});
	}
	
	protected CounterTrace BeforeInstAbsPattern(PatternType pattern, CDD q, CDD r, CDD p, CDD s){ 
		pattern.setEffect(r);
		return new CounterTrace(new CounterTrace.DCPhase[] {
    		    new CounterTrace.DCPhase(r.negate()),
    		    new CounterTrace.DCPhase(p.and(r.negate())),
    		    new CounterTrace.DCPhase(r.negate()),
    		    new CounterTrace.DCPhase(r),
    		    new CounterTrace.DCPhase()
    		 });    	
	}
	
	protected CounterTrace AfterUntilInstAbsPattern(PatternType pattern, CDD q, CDD r, CDD p, CDD s){ 
		return new CounterTrace(new CounterTrace.DCPhase[] {
	               	    new CounterTrace.DCPhase(),
	               	    new CounterTrace.DCPhase(q.and(r.negate())),
	               	    new CounterTrace.DCPhase(r.negate()),
	               	    new CounterTrace.DCPhase(p.and(r.negate())),
	               	    new CounterTrace.DCPhase()
	               	});   
	}

	protected CounterTrace AfterInstAbsPattern(PatternType pattern, CDD q, CDD r, CDD p, CDD s){ 
		pattern.setEffect(r);
		return new CounterTrace(new CounterTrace.DCPhase[] {
	    	    new CounterTrace.DCPhase(),
	    	    new CounterTrace.DCPhase(q),
	    	    new CounterTrace.DCPhase(),
	    	    new CounterTrace.DCPhase(p),
	    	    new CounterTrace.DCPhase()
	    	});    	
	}
	
	protected CounterTrace BetweenInstAbsPattern(PatternType pattern, CDD q, CDD r, CDD p, CDD s){ 
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
	protected CounterTrace GlobalInvariantPattern(PatternType pattern, CDD q, CDD r, CDD p, CDD s){ 
		pattern.setEffect(s);
		return new CounterTrace(new CounterTrace.DCPhase[] {
				    new CounterTrace.DCPhase(),
				    new CounterTrace.DCPhase(p.and(s.negate())),
				    new CounterTrace.DCPhase()
				});
	}
	
	protected CounterTrace BeforeInvariantPattern(PatternType pattern, CDD q, CDD r, CDD p, CDD s){ 
		//Before R it is always the case that if p holds then s holds as well.
		return new CounterTrace(new CounterTrace.DCPhase[] {
    		    new CounterTrace.DCPhase(r.negate()),
    		    new CounterTrace.DCPhase(p.and(s.negate()).and(r.negate())),
    		    new CounterTrace.DCPhase(r.negate()),
    		    new CounterTrace.DCPhase(r),
    		    new CounterTrace.DCPhase()
    		 });    	
	}
	
	protected CounterTrace AfterUntilInvariantPattern(PatternType pattern, CDD q, CDD r, CDD p, CDD s){ 
		pattern.setEffect(s);
		return new CounterTrace(new CounterTrace.DCPhase[] {
           	    new CounterTrace.DCPhase(),
           	    new CounterTrace.DCPhase(q.and(r.negate())),
           	    new CounterTrace.DCPhase(r.negate()),
           	    new CounterTrace.DCPhase(p.and(r.negate()).and(s.negate())),
           	    new CounterTrace.DCPhase()
           	});    	
	}

	protected CounterTrace AfterInvariantPattern(PatternType pattern, CDD q, CDD r, CDD p, CDD s){ 
		pattern.setEffect(s);
		return new CounterTrace(new CounterTrace.DCPhase[] {
	    	    new CounterTrace.DCPhase(),
	    	    new CounterTrace.DCPhase(q),
	    	    new CounterTrace.DCPhase(),
	    	    new CounterTrace.DCPhase(p.and(s.negate())),
	    	    new CounterTrace.DCPhase()
	    	});    	
	}
	
	protected CounterTrace BetweenInvariantPattern(PatternType pattern, CDD q, CDD r, CDD p, CDD s){ 
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
