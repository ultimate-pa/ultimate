package de.uni_freiburg.informatik.ultimate.reqtotestpowerset.graph;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeGlob;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.BndResponsePatternUT;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InitializationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InvariantPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.UniversalityPattern;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.pea2boogie.CddToSmt;

public class BuchiGraph {
	
	private final ILogger mLogger;
	private final CddToSmt mCddToSmt;
	private final Script mScript;
	
	public BuchiGraph(final ILogger logger, Script script, CddToSmt cddToSmt) {
		mLogger = logger;
		mCddToSmt = cddToSmt;
		mScript = script;
	}
	
	public List<GuardGraph> patternListToBuechi(List<PatternType> patternList){
		final List<GuardGraph> gs = new ArrayList<GuardGraph>();
		for (PatternType pattern: patternList) {
			if (! (pattern instanceof InitializationPattern)){
				GuardGraph aut = patternToAutomaton(pattern);
				if(aut != null) {
					gs.add(aut);
				}
			}
		}
		return gs;
	}
	
	/*								  Global		After		Until		After Until
		InvariantPattern				X
  		UniversalityPattern				X
  		BndResponsePatternUT			X
  	*/
	
	public GuardGraph patternToAutomaton(PatternType pattern) {
		if(pattern instanceof InvariantPattern){
			return makeInvariantPatternAutomaton(pattern);
		} else if(pattern instanceof UniversalityPattern) {
			return makeUniversalityPatternAutomaton(pattern);
		} else if(pattern instanceof BndResponsePatternUT) {
			return makeBndResponsePatternUTAutomaton(pattern);
		} else {
			throw new RuntimeException("Pattern type -" + pattern.toString() + "- not supported!");
		}
	}

	/*
	 * {scope}, it is always the case that if "R" holds, then "S" holds in the next step.
	 *  
	 *  G(R -> XS)
	 */
	private GuardGraph makeBndResponsePatternUTAutomaton(PatternType pattern) {
		if (pattern.getScope() instanceof SrParseScopeGlob) {
			final List<CDD> args = pattern.getCdds();
			// Terms - also known as edge labels
			final Term R = mCddToSmt.toSmt(args.get(1));
			final Term S = mCddToSmt.toSmt(args.get(0));
			final Term nR = SmtUtils.not(mScript, R);
			
			// States 
			final GuardGraph q0 = new GuardGraph(0);
			final GuardGraph q1 = new GuardGraph(1);
			
			// Edges
			q0.connectOutgoing(q0, nR);
			q0.connectOutgoing(q1, R);
			q1.connectOutgoing(q1, SmtUtils.and(mScript, R, S));
			q1.connectOutgoing(q0, SmtUtils.and(mScript, nR, S));
			
			return q0;
		} else {
			mLogger.warn("Scope not implemented: " + pattern.getScope().toString());
			return null;
		}
	}
	
	/*
	 *  * {scope}, it is always the case that if "R" holds, then "S" holds as well.
	 *  
	 *  G(R -> S)
	 */
	private GuardGraph makeInvariantPatternAutomaton(PatternType pattern) {
		if(pattern.getScope() instanceof SrParseScopeGlob) {
			final List<CDD> args = pattern.getCdds();
			// Terms
			final Term R = mCddToSmt.toSmt(args.get(1));
			final Term S = mCddToSmt.toSmt(args.get(0));
			final Term nR = SmtUtils.not(mScript, R);
			
			// States 
			final GuardGraph q0 = new GuardGraph(0);
			
			// Edges
			q0.connectOutgoing(q0, SmtUtils.or(mScript, SmtUtils.or(mScript, nR, S)));
			
			return q0;
		} else {
			mLogger.warn("Scope not implemented: " + pattern.getScope().toString());
			return null;
		}
	}

	/*
	 *  * {scope}, it is always the case that "S" holds.
	 *  
	 *  G(S)
	 */
	private GuardGraph makeUniversalityPatternAutomaton(PatternType pattern) {
		if(pattern.getScope() instanceof SrParseScopeGlob) {
			final List<CDD> args = pattern.getCdds();
			
			// Terms
			final Term S = mCddToSmt.toSmt(args.get(0)); 
			
			// States
			final GuardGraph q0 = new GuardGraph(0);
			
			// Edges
			q0.connectOutgoing(q0, S);
			
			return q0;
		} else {
			mLogger.warn("Scope not implemented: " + pattern.getScope().toString());
			return null;
		}
	}
}
