package de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.PEATestTransformer.SystemInformation;
import pea.CDD;
import pea.CounterTrace;
import pea.PhaseEventAutomata;
import pea.Trace2PEACompiler;
import srParse.srParseScopeAfter;
import srParse.srParseScopeAfterUntil;
import srParse.srParseScopeBefore;
import srParse.srParseScopeBetween;
import srParse.srParseScopeGlob;
import srParse.pattern.InstAbsPattern;
import srParse.pattern.InvariantPattern;
import srParse.pattern.PatternType;
import srParse.pattern.UniversalityPattern;

/***
 * Easily modifiable requirements pattern to Pea transformation.
 * 
 * @author Langenfeld
 * 
 * TODO: complete rewrite of pattern! 
 *
 */
public class BasicTransformer {
	Trace2PEACompiler compiler = new Trace2PEACompiler();
	
	/**
	 * Translates a pattern into a Phase Event Automaton
	 * @param pattern spl pattern
	 * @return automaton of pattern
	 */
	public final List<PhaseEventAutomata> translate(ArrayList<PatternType> patterns){
		ArrayList<PhaseEventAutomata> peas = new ArrayList<PhaseEventAutomata>();
		this.preProcess(patterns);
		for(PatternType pattern : patterns)
		{
			peas.add(this.translateSwitch(pattern));
		}
		return postProcess(patterns, peas);
	}
	
	/*
	 * This Method can be extended to analyze the input automata before the translation 
	 * is begun e.g. to collect all vairables.
	 */
	protected void preProcess(ArrayList<PatternType> patterns){
	}
	
	/*
	 * This Method can be extended to postprocess the output, 
	 * e.g. to add automata for special purposes
	 */
	protected ArrayList<PhaseEventAutomata> postProcess(ArrayList<PatternType> patterns, ArrayList<PhaseEventAutomata> peas){
		return peas; 
	}


	private PhaseEventAutomata translateSwitch(PatternType pattern){
		//get CDDs
		CDD p = null;
		if (pattern.getCdds().size() > 1)  p =  pattern.getCdds().get(1);
		CDD q = pattern.getScope().getCdd1(); 
		CDD r = pattern.getScope().getCdd2();
		CDD s = pattern.getCdds().get(0);
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
				return this.BeforeInvariantPattern(pattern, p, q, r, s);			//test [broken]
			} else if (pattern.getScope().getClass() == srParseScopeAfterUntil.class){	
				return this.AfterUntilInvariantPattern(pattern, p, q, r, s);		//test []
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
				return this.AfterUntilInstAbsPattern(pattern, p, q, r, s);			//test [broken]
			} else if (pattern.getScope().getClass() == srParseScopeAfter.class){
				return this.AfterInstAbsPattern(pattern, p, q, r, s);				//test [yes]
			} else if (pattern.getScope().getClass() == srParseScopeBetween.class){	
				return this.BetweenInstAbsPattern(pattern, p, q, r, s);				//test [broken]
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
			
		} else {
			throw new UnsupportedOperationException("Pattern not implemented");
		}
	}
	
	//Universality Pattern
	//TODO: not tested but taken from pattern pdf, test asap
	protected PhaseEventAutomata GlobalUniversality(PatternType pattern, CDD p, CDD q, CDD r, CDD s){ 
		CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
			    new CounterTrace.DCPhase(),
			    new CounterTrace.DCPhase(s.negate()),
			    new CounterTrace.DCPhase()
			});
			return compiler.compile("GlobalUniverslity", ct);
	}
	//TODO: not tested but taken from pattern pdf, test asap
	protected PhaseEventAutomata BeforeUniversality(PatternType pattern, CDD p, CDD q, CDD r, CDD s){ 
		CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
			    new CounterTrace.DCPhase(q.negate()),
			    new CounterTrace.DCPhase(q.negate().and(s)),
			    new CounterTrace.DCPhase()
			});
			return compiler.compile("BeforeUniverstality", ct);
	}
	//TODO: not tested but taken from pattern pdf, test asap
	protected PhaseEventAutomata AfterUniversality(PatternType pattern, CDD p, CDD q, CDD r, CDD s){ 
		CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
				new CounterTrace.DCPhase(),
			    new CounterTrace.DCPhase(q),
			    new CounterTrace.DCPhase(),
			    new CounterTrace.DCPhase(s.negate()),
			    new CounterTrace.DCPhase()
			});
			return compiler.compile("AfterUniverstality", ct);
	}
	//TODO: not tested but taken from pattern pdf, test asap
	protected PhaseEventAutomata BetweenUniversality(PatternType pattern, CDD p, CDD q, CDD r, CDD s){ 
		CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
				new CounterTrace.DCPhase(),
			    new CounterTrace.DCPhase(q.and(r.negate())),
			    new CounterTrace.DCPhase(r.negate()),
			    new CounterTrace.DCPhase(r.negate().and(s.negate())),
			    new CounterTrace.DCPhase(r.negate()),
			    new CounterTrace.DCPhase(r),
			    new CounterTrace.DCPhase()
			});
			return compiler.compile("AfterUniverstality", ct);
	}
	//TODO: not tested but taken from pattern pdf, test asap
	protected PhaseEventAutomata AfterUntilUniversality(PatternType pattern, CDD p, CDD q, CDD r, CDD s){ 
		CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
				new CounterTrace.DCPhase(),
			    new CounterTrace.DCPhase(r.negate().and(q)),
			    new CounterTrace.DCPhase(r.negate()),
			    new CounterTrace.DCPhase(r.negate().and(s.negate())),
			    new CounterTrace.DCPhase()
			});
			return compiler.compile("AfterUniverstality", ct);
	}

	
	//AbsencePattern (InstAbsPattern)
	protected PhaseEventAutomata GlobalInstAbsPattern(PatternType pattern, CDD p, CDD q, CDD r, CDD s){ 
		CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
			    new CounterTrace.DCPhase(),
			    new CounterTrace.DCPhase(s),
			    new CounterTrace.DCPhase()
			});
			return compiler.compile("AbsenceGlob", ct);
	}
	
	protected PhaseEventAutomata BeforeInstAbsPattern(PatternType pattern, CDD p, CDD q, CDD r, CDD s){ 
		CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
    		    new CounterTrace.DCPhase(r.negate()),
    		    new CounterTrace.DCPhase(s.and(r.negate())),
    		    new CounterTrace.DCPhase(r.negate()),
    		    new CounterTrace.DCPhase(r),
    		    new CounterTrace.DCPhase()
    		 });    	
    		return compiler.compile("TAbsenceBefore", ct);
	}
	
	protected PhaseEventAutomata AfterUntilInstAbsPattern(PatternType pattern, CDD p, CDD q, CDD r, CDD s){ 
	        	CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
	               	    new CounterTrace.DCPhase(),
	               	    new CounterTrace.DCPhase(q.and(r.negate())),
	               	    new CounterTrace.DCPhase(r.negate()),
	               	    new CounterTrace.DCPhase(s.and(r.negate())),
	               	    new CounterTrace.DCPhase()
	               	});   
	               	return compiler.compile("TAbsenceUntil", ct);
	}

	protected PhaseEventAutomata AfterInstAbsPattern(PatternType pattern, CDD p, CDD q, CDD r, CDD s){ 
		CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
	    	    new CounterTrace.DCPhase(),
	    	    new CounterTrace.DCPhase(q),
	    	    new CounterTrace.DCPhase(),
	    	    new CounterTrace.DCPhase(s),
	    	    new CounterTrace.DCPhase()
	    	});    	
	    	return compiler.compile("TAbsenceAfter", ct);
	}
	
	protected PhaseEventAutomata BetweenInstAbsPattern(PatternType pattern, CDD p, CDD q, CDD r, CDD s){ 
		CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
    	  	    new CounterTrace.DCPhase(),
    	   	    new CounterTrace.DCPhase(q.and(r.negate())),
    	   	    new CounterTrace.DCPhase(r.negate()),
    	   	    new CounterTrace.DCPhase(s.and(r.negate())),
    	   	    new CounterTrace.DCPhase(r.negate()),
    	   	    new CounterTrace.DCPhase(r),
    	  	  new CounterTrace.DCPhase()
    	   	});    	
    	   	return compiler.compile("TAbsBet", ct);
	}
	
	//InvariantPattern
	// Is absence pattern with absencePattern(P.and(S.negate()),Q,R, scope);
	/* public PhaseEventAutomata invariantPattern(CDD P, CDD Q, CDD R, CDD S, String scope) {
    	 ctA = absencePattern(P.and(S.negate()),Q,R, scope);
    	 */
	protected PhaseEventAutomata GlobalInvariantPattern(PatternType pattern, CDD p, CDD q, CDD r, CDD s){ 
			CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
				    new CounterTrace.DCPhase(),
				    new CounterTrace.DCPhase(p.and(s.negate())),
				    new CounterTrace.DCPhase()
				});
			return compiler.compile("InvariantGlob", ct);
	}
	
	protected PhaseEventAutomata BeforeInvariantPattern(PatternType pattern, CDD p, CDD q, CDD r, CDD s){ 
		CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
    		    new CounterTrace.DCPhase(p.negate()),
    		    new CounterTrace.DCPhase(p.and(s.negate()).and(q.negate())),
    		    new CounterTrace.DCPhase(p.negate()),
    		    new CounterTrace.DCPhase()
    		 });    	
    		return compiler.compile("TAbsenceBefore", ct);
	}
	
	protected PhaseEventAutomata AfterUntilInvariantPattern(PatternType pattern, CDD p, CDD q, CDD r, CDD s){ 
		CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
           	    new CounterTrace.DCPhase(),
           	    new CounterTrace.DCPhase(q.and(r.negate())),
           	    new CounterTrace.DCPhase(r.negate()),
           	    new CounterTrace.DCPhase(s.and(r.negate())),
           	    new CounterTrace.DCPhase()
           	});    	
           	return compiler.compile("TAbsenceUntil", ct);
	}

	//TODO: not tested but taken from pattern pdf, test asap
	protected PhaseEventAutomata AfterInvariantPattern(PatternType pattern, CDD p, CDD q, CDD r, CDD s){ 
		CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
	    	    new CounterTrace.DCPhase(),
	    	    new CounterTrace.DCPhase(q),
	    	    new CounterTrace.DCPhase(),
	    	    new CounterTrace.DCPhase(p.and(s.negate())),
	    	    new CounterTrace.DCPhase()
	    	});    	
	    	return compiler.compile("TAbsenceAfter", ct);
	}
	
	protected PhaseEventAutomata BetweenInvariantPattern(PatternType pattern, CDD p, CDD q, CDD r, CDD s){ 
		CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
    	  	    new CounterTrace.DCPhase(),
    	   	    new CounterTrace.DCPhase(q.and(r.negate())),
    	   	    new CounterTrace.DCPhase(r.negate()),
    	   	    new CounterTrace.DCPhase(s.and(r.negate())),
    	   	    new CounterTrace.DCPhase(r.negate()),
    	   	    new CounterTrace.DCPhase(r),
    	  	  new CounterTrace.DCPhase()
    	   	});    	
    	   	return compiler.compile("TAbsBet", ct);
	}
	
	
	

	

}
