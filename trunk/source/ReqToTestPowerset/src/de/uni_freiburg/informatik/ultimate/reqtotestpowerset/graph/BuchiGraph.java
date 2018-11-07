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
import de.uni_freiburg.informatik.ultimate.reqtotest.req.ReqGuardGraph;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.ReqSymbolTable;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.TimedLabel;

public class BuchiGraph {
	
	private final ILogger mLogger;
	private final CddToSmt mCddToSmt;
	private final ReqSymbolTable mReqSymbolTable;
	private final Script mScript;
	
	public BuchiGraph(final ILogger logger, Script script, CddToSmt cddToSmt,
			ReqSymbolTable reqSymbolTable) {
		mLogger = logger;
		mCddToSmt = cddToSmt;
		mScript = script;
		mReqSymbolTable = reqSymbolTable;
	}
	
	public List<ReqGuardGraph> patternListToBuechi(List<PatternType> patternList){
		final List<ReqGuardGraph> gs = new ArrayList<ReqGuardGraph>();
		for (PatternType pattern: patternList) {
			if (! (pattern instanceof InitializationPattern)){
				ReqGuardGraph aut = patternToAutomaton(pattern);
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
	
	public ReqGuardGraph patternToAutomaton(PatternType pattern) {
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
	private ReqGuardGraph makeBndResponsePatternUTAutomaton(PatternType pattern) {
		if (pattern.getScope() instanceof SrParseScopeGlob) {
			final List<CDD> args = pattern.getCdds();
			// Terms - also known as edge labels
			final Term R = mCddToSmt.toSmt(args.get(1));
			final Term S = mCddToSmt.toSmt(args.get(0));
			final Term nR = SmtUtils.not(mScript, R);
			final Term RandS = SmtUtils.and(mScript, R, S);
			final Term nRandS = SmtUtils.and(mScript, nR, S);
			
			// States 
			final ReqGuardGraph q0 = new ReqGuardGraph(0);
			final ReqGuardGraph q1 = new ReqGuardGraph(1);
			// TODO is a 3rd State (error-state) needed?
			
			// 
			q0.connectOutgoing(q0, new TimedLabel(nR));
			q0.connectOutgoing(q1, new TimedLabel(R));
			q1.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, R, S)));
			q1.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, nR, S)));
			
			/*for debug TODO remove later
			mLogger.warn(R.toString());
			mLogger.warn(S.toString());
			mLogger.warn("-------------------");
			*/
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
	private ReqGuardGraph makeInvariantPatternAutomaton(PatternType pattern) {
		// TODO Auto-generated method stub
		return null;
	}

	/*
	 *  * {scope}, it is always the case that "S" holds.
	 *  
	 *  G(S)
	 */
	private ReqGuardGraph makeUniversalityPatternAutomaton(PatternType pattern) {
		// TODO Auto-generated method stub
		return null;
	}
}
