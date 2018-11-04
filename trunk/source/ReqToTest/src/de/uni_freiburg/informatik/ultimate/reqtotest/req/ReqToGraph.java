package de.uni_freiburg.informatik.ultimate.reqtotest.req;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeGlob;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.BndInvariancePattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.BndResponsePatternTT;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.BndResponsePatternTU;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.BndResponsePatternUT;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InitializationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InstAbsPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InvariantPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.UniversalityPattern;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieDeclarations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.pea2boogie.CddToSmt;
import de.uni_freiburg.informatik.ultimate.reqtotest.graphtransformer.ThreeValuedAuxVarGen;

public class ReqToGraph {
	
	private final ILogger mLogger;
	
	private final CddToSmt mCddToSmt;

	private final ThreeValuedAuxVarGen mThreeValuedAuxVarGen;
	private final Script mScript;
	
	public ReqToGraph(final ILogger logger, ThreeValuedAuxVarGen threeValuedAuxVarGen, Script script, CddToSmt cddToSmt){
		mLogger = logger;
		mThreeValuedAuxVarGen = threeValuedAuxVarGen;
		mCddToSmt = cddToSmt;
		mScript = script;
		
	}
	
	public List<ReqGuardGraph> patternListToBuechi(List<PatternType> patternList){
		final List<ReqGuardGraph> gs = new ArrayList<ReqGuardGraph>();
		for (PatternType pattern: patternList) {
			if (! (pattern instanceof InitializationPattern)){
				gs.add(patternToTestAutomaton(pattern));
			}
		}
		return gs;
	}
	
	 
	/*								  Global		After		Until		After Until
	    BndInvariancePattern			X
    	BndResponsePatternTT			X
    	BndResponsePatternUT			X
       	BndResponsePatternTU 			X
    	InvariantPattern				X
    	InstAbsPattern					X
      	UniversalityPattern				X
	*/

	public ReqGuardGraph patternToTestAutomaton(PatternType pattern){
		if(pattern instanceof InvariantPattern){
			return getInvariantPattern(pattern);
		} else if(pattern instanceof BndResponsePatternUT){
			return getBndResponsePatternUTPattern(pattern);
		} else if(pattern instanceof BndInvariancePattern){
			return getBndInvariance(pattern);		 
		}else if(pattern instanceof BndResponsePatternTT){
			return getBndResponsePatternTTPattern(pattern);
		} else if(pattern instanceof UniversalityPattern){
			return getUniversalityPattern(pattern);
		} else if (pattern instanceof InstAbsPattern){
			return getInstAbsPattern(pattern);
		} else if(pattern instanceof BndResponsePatternTU){
			return getBndResponsePatternTUPattern(pattern);
		} else {
			throw new RuntimeException("Pattern type is not supported at:" + pattern.toString());
		}
	}
	
	/*
	 * "{scope}, it is always the case that if "R" holds for at least "c1" time units, then "S" holds afterwards for at
	 * least "c2" time units
	 */
	private ReqGuardGraph getBndResponsePatternTTPattern(PatternType pattern){
		if(pattern.getScope() instanceof SrParseScopeGlob) {
			final List<CDD> args = pattern.getCdds();
			final Term R = mCddToSmt.toSmt(args.get(1));
			final Term S = mCddToSmt.toSmt(args.get(0)); 
			//create states to identify automaton
			final ReqGuardGraph q0 = new ReqGuardGraph(0);
			final ReqGuardGraph q1 = new ReqGuardGraph(1);
			final ReqGuardGraph q2 = new ReqGuardGraph(2);
			final ReqGuardGraph qw = new ReqGuardGraph(3);
			//create effect guards
			mThreeValuedAuxVarGen.setEffectLabel(q0, S);
			final String durationTrigger = pattern.getDuration().get(0);
			final String durationEffect = pattern.getDuration().get(1);
			TermVariable clockIdent = mThreeValuedAuxVarGen.generateClockIdent(q0);
			//assuming RT-Consistency <>(\leq t) can be transformed into <>(==t)
			Term triggerLess = SmtUtils.less(mScript, clockIdent, mScript.numeral(durationTrigger));
			Term triggerEq = SmtUtils.binaryEquality(mScript, clockIdent, mScript.numeral(durationTrigger));	
			Term effectLess = SmtUtils.less(mScript, clockIdent, mScript.numeral(durationEffect));
			Term effectEq = SmtUtils.binaryEquality(mScript, clockIdent, mScript.numeral(durationEffect));
					//define labels 
			final Term dS = mThreeValuedAuxVarGen.getDefineGuard(q0);
			final Term ndS = mThreeValuedAuxVarGen.getNonDefineGuard(q0);
			//normal labels
			final Term uR = mThreeValuedAuxVarGen.getUseGuard(R);
			final Term nuR = SmtUtils.not(mScript, uR); 
			final Term nR = SmtUtils.not(mScript, R);
			
			q0.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, ndS, uR, nR)));
			q0.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, uR, R, ndS), clockIdent));
			q1.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, uR, R, ndS, triggerLess)));
			q1.connectOutgoing(q2, new TimedLabel(SmtUtils.and(mScript, uR, R, triggerEq), clockIdent));
			q2.connectOutgoing(q2, new TimedLabel(SmtUtils.and(mScript,  dS, S, effectLess)));
			q2.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript,  dS, S, effectEq)));
			
			q0.connectOutgoing(qw, new TimedLabel(SmtUtils.and(mScript, nuR, ndS)));
			qw.connectOutgoing(qw, new TimedLabel(SmtUtils.and(mScript, nuR, ndS)));
			qw.connectOutgoing(q0, new TimedLabel(SmtUtils.or(mScript, uR, nR, ndS)));
			qw.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, uR, R, ndS), clockIdent));
			
			return q0;		
		} else {
			throw new RuntimeException("Scope not implemented");
		}
	}
	
	/*
	 * {scope}, it is always the case that if "R" holds for at least "c1" time units, then "S" holds afterwards.
	 */
	private ReqGuardGraph getBndResponsePatternTUPattern(PatternType pattern){
		if(pattern.getScope() instanceof SrParseScopeGlob) {
			final List<CDD> args = pattern.getCdds();
			final Term R = mCddToSmt.toSmt(args.get(1));
			final Term S = mCddToSmt.toSmt(args.get(0)); 
			//create states to identify automaton
			final ReqGuardGraph q0 = new ReqGuardGraph(0);
			final ReqGuardGraph q1 = new ReqGuardGraph(1);
			final ReqGuardGraph q2 = new ReqGuardGraph(2);
			final ReqGuardGraph qw = new ReqGuardGraph(3);
			//create effect guards
			mThreeValuedAuxVarGen.setEffectLabel(q0, S);
			final String duration = pattern.getDuration().get(0);
			TermVariable clockIdent = mThreeValuedAuxVarGen.generateClockIdent(q0);
			//assuming RT-Consistency <>(\leq t) can be transformed into <>(==t)
			Term triggerLess = SmtUtils.less(mScript, clockIdent, mScript.numeral(duration));
			Term triggerEq = SmtUtils.binaryEquality(mScript, clockIdent, mScript.numeral(duration));	
					//define labels 
			final Term dS = mThreeValuedAuxVarGen.getDefineGuard(q0);
			final Term ndS = mThreeValuedAuxVarGen.getNonDefineGuard(q0);
			//normal labels
			final Term uR = mThreeValuedAuxVarGen.getUseGuard(R);
			final Term nuR = SmtUtils.not(mScript, uR); 
			final Term nR = SmtUtils.not(mScript, R);
			
			q0.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, ndS, uR, nR)));
			q0.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, uR, R, ndS), clockIdent));
			q1.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, uR, R, ndS, triggerLess)));
			q1.connectOutgoing(q2, new TimedLabel(SmtUtils.and(mScript, uR, R, ndS, triggerEq)));
			q1.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, nR, uR, ndS, triggerLess)));
			q2.connectOutgoing(q2, new TimedLabel(SmtUtils.and(mScript,  uR, R, dS, S)));
			q2.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript,  nR, uR, S, dS)));
			
			q0.connectOutgoing(qw, new TimedLabel(SmtUtils.and(mScript, nuR, ndS)));
			q1.connectOutgoing(qw, new TimedLabel(SmtUtils.and(mScript, nuR, ndS)));
			qw.connectOutgoing(qw, new TimedLabel(SmtUtils.and(mScript, nuR, ndS)));
			qw.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, uR, nR, ndS)));
			qw.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, uR, R, ndS), clockIdent));
			
			
			return q0;		
		} else {
			throw new RuntimeException("Scope not implemented");
		}
	}
	
	/*
	 *  * {scope}, it is always the case that if "R" holds, then "S" holds for at least "c1" time units.
	 */
	private ReqGuardGraph getBndInvariance(PatternType pattern){
		if(pattern.getScope() instanceof SrParseScopeGlob) {
			final List<CDD> args = pattern.getCdds();
			final Term R = mCddToSmt.toSmt(args.get(1));
			final Term S = mCddToSmt.toSmt(args.get(0)); 
			//create states to identify automaton
			final ReqGuardGraph q0 = new ReqGuardGraph(0);
			final ReqGuardGraph q1 = new ReqGuardGraph(1);
			final ReqGuardGraph qw = new ReqGuardGraph(2);
			//create effect guards
			mThreeValuedAuxVarGen.setEffectLabel(q0, S);
			final String duration = pattern.getDuration().get(0);
			TermVariable clockIdent = mThreeValuedAuxVarGen.generateClockIdent(q0);
			Term clockGuard = SmtUtils.leq(mScript, clockIdent, mScript.numeral(duration));	
			Term clockGuardGeq = SmtUtils.greater(mScript, clockIdent, mScript.numeral(duration));	
					//define labels 
			final Term dS = mThreeValuedAuxVarGen.getDefineGuard(q0);
			final Term ndS = mThreeValuedAuxVarGen.getNonDefineGuard(q0);
			//normal labels
			final Term uR = mThreeValuedAuxVarGen.getUseGuard(R);
			final Term nuR = SmtUtils.not(mScript, uR); 
			final Term nR = SmtUtils.not(mScript, R);
			
			q0.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, uR, nR, ndS)));
			q0.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, uR, R, dS, S), clockIdent));
			q1.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, clockGuard, S, dS, uR, nR)));
			q1.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, clockGuard, S, dS, uR, R), clockIdent));
			q1.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, clockGuardGeq, uR, nR, ndS)));
			
			q0.connectOutgoing(qw, new TimedLabel(SmtUtils.and(mScript, nuR, ndS)));
			qw.connectOutgoing(qw, new TimedLabel(SmtUtils.and(mScript, nuR, ndS)));
			qw.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, uR, nR, ndS)));
			qw.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, uR, R, dS, S), clockIdent));
			
			return q0;		
		} else {
			throw new RuntimeException("Scope not implemented");
		}
	}
	
	/*
	 * {scope}, it is always the case that if "R" holds, then "S" holds after at most "c1" time units.
	 *  
	 * Assuming stability of output ( R, R & S, R & !S, R & S,.....) not intended behavior
	 */
	private ReqGuardGraph getBndResponsePatternUTPattern(PatternType pattern){
		if(pattern.getScope() instanceof SrParseScopeGlob) {
			final List<CDD> args = pattern.getCdds();
			final Term R = mCddToSmt.toSmt(args.get(1));
			final Term S = mCddToSmt.toSmt(args.get(0)); 
			//create states to identify automaton
			final ReqGuardGraph q0 = new ReqGuardGraph(0);
			final ReqGuardGraph q1 = new ReqGuardGraph(1);
			final ReqGuardGraph q2 = new ReqGuardGraph(2);
			final ReqGuardGraph qw = new ReqGuardGraph(3);
			//create effect guards
			mThreeValuedAuxVarGen.setEffectLabel(q0, S);
			final String duration = pattern.getDuration().get(0);
			TermVariable clockIdent = mThreeValuedAuxVarGen.generateClockIdent(q0);
			//assuming RT-Consistency <>(\leq t) can be transformed into <>(==t)
			Term clockGuardLess = SmtUtils.less(mScript, clockIdent, mScript.numeral(duration));
			Term clockGuardEq = SmtUtils.binaryEquality(mScript, clockIdent, mScript.numeral(duration));	
			Term clockGuardGeq = SmtUtils.geq(mScript, clockIdent, mScript.numeral(duration));
			//define labels 
			final Term dS = mThreeValuedAuxVarGen.getDefineGuard(q0);
			final Term ndS = mThreeValuedAuxVarGen.getNonDefineGuard(q0);
			//normal labels
			final Term uR = mThreeValuedAuxVarGen.getUseGuard(R);
			final Term nuR = SmtUtils.not(mScript, uR); 
			final Term uS = mThreeValuedAuxVarGen.getUseGuard(S);
			final Term nR = SmtUtils.not(mScript, R);
			
			//regular automaton
			q0.connectOutgoing(q0, new TimedLabel(
					SmtUtils.and(mScript, ndS,
							SmtUtils.or(mScript,
								SmtUtils.and(mScript, uR, nR),
								SmtUtils.and(mScript, uS, S))
									)));
			q0.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, uR, R, ndS), clockIdent));
			q1.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript,
													SmtUtils.or(mScript,
															SmtUtils.and(mScript, R, uR, ndS, clockGuardLess),
															SmtUtils.and(mScript, R, uR, S, dS, clockGuardGeq))
																)));
			q1.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, nR, uR, ndS, clockGuardGeq)));
			q1.connectOutgoing(q2, new TimedLabel(SmtUtils.and(mScript, clockGuardLess, ndS, 
													SmtUtils.or(mScript, 
															SmtUtils.and(mScript, uR, nR),
															SmtUtils.and(mScript, nuR))
																)));
			q2.connectOutgoing(q2, new TimedLabel(SmtUtils.and(mScript, clockGuardLess, ndS)));
			q2.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, clockGuardEq, S, dS)));
			// uncertainty
			q0.connectOutgoing(qw, new TimedLabel(SmtUtils.and(mScript, nuR, ndS)));
			qw.connectOutgoing(qw, new TimedLabel(SmtUtils.and(mScript, nuR, ndS)));
			qw.connectOutgoing(q0, new TimedLabel(SmtUtils.or(mScript, 
					SmtUtils.and(mScript, uR, nR, ndS),
					SmtUtils.and(mScript, uS, S, ndS))));
			qw.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, uR, R, ndS), clockIdent));
			
			return q0;		
		} else {
			throw new RuntimeException("Scope not implemented");
		}
	}
	
	/*
	 *  * {scope}, it is always the case that if "R" holds, then "S" holds as well.
	 */
	private ReqGuardGraph getInvariantPattern(PatternType pattern){
		if(pattern.getScope() instanceof SrParseScopeGlob) {
			final List<CDD> args = pattern.getCdds();
			final Term R = mCddToSmt.toSmt(args.get(1));
			final Term S = mCddToSmt.toSmt(args.get(0)); 
			final ReqGuardGraph q0 = new ReqGuardGraph(0);
			mThreeValuedAuxVarGen.setEffectLabel(q0, S);
			//define labels 
			final Term dS = mThreeValuedAuxVarGen.getDefineGuard(q0);
			final Term ndS = mThreeValuedAuxVarGen.getNonDefineGuard(q0);
			//normal labels
			final Term uR = mThreeValuedAuxVarGen.getUseGuard(R);
			final Term nuR = SmtUtils.not(mScript, uR); 
			final Term uS = mThreeValuedAuxVarGen.getUseGuard(S);
			final Term nR = SmtUtils.not(mScript, R);
			q0.connectOutgoing(q0, new TimedLabel(SmtUtils.or(mScript,
					SmtUtils.and(mScript, nuR, ndS), 
					SmtUtils.and(mScript, uR, R, ndS, S),
					SmtUtils.and(mScript, uR, nR, ndS),
					SmtUtils.and(mScript, S, uS, ndS))));
			return q0;
		} else {
			throw new RuntimeException("Scope not implemented");
		}
	}
	
	/*
	 *  * {scope}, it is always the case that if "S" holds.
	 */
	private ReqGuardGraph getUniversalityPattern(PatternType pattern){
		if(pattern.getScope() instanceof SrParseScopeGlob) {
			final List<CDD> args = pattern.getCdds();
			final Term S = mCddToSmt.toSmt(args.get(0)); 
			final ReqGuardGraph q0 = new ReqGuardGraph(0);
			mThreeValuedAuxVarGen.setEffectLabel(q0, S);
			//define labels 
			final Term dS = mThreeValuedAuxVarGen.getDefineGuard(q0);
			//normal labels
			q0.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, S, dS)));
			return q0;
		} else {
			throw new RuntimeException("Scope not implemented");
		}
	}
	
	/*
	 *  * {scope}, it is never the case that if "S" holds.
	 */
	private ReqGuardGraph getInstAbsPattern(PatternType pattern){
		if(pattern.getScope() instanceof SrParseScopeGlob) {
			final List<CDD> args = pattern.getCdds();
			final Term S = mCddToSmt.toSmt(args.get(0)); 
			final ReqGuardGraph q0 = new ReqGuardGraph(0);
			mThreeValuedAuxVarGen.setEffectLabel(q0, S);
			//define labels 
			final Term dS = mThreeValuedAuxVarGen.getDefineGuard(q0);
			//normal labels
			final Term nS = SmtUtils.not(mScript, S);
			q0.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, nS, dS)));
			return q0;
		} else {
			throw new RuntimeException("Scope not implemented");
		}
	}
	
	/*	This pattern is for discrete Step LTL
	 *  * {scope}, it is always the case that if "R" holds, then "S" holds in the next Step.
	 */
	private ReqGuardGraph getImmediateResponsePatternToAutomaton(PatternType pattern){
		if(pattern.getScope() instanceof SrParseScopeGlob) {
			final List<CDD> args = pattern.getCdds();
			final Term R = mCddToSmt.toSmt(args.get(1));
			final Term S = mCddToSmt.toSmt(args.get(0)); 
			//create states to identify automaton
			final ReqGuardGraph q0 = new ReqGuardGraph(0);
			final ReqGuardGraph q1 = new ReqGuardGraph(1);
			final ReqGuardGraph qw = new ReqGuardGraph(2);
			//create effect guards
			mThreeValuedAuxVarGen.setEffectLabel(q0, S);
			//define labels 
			final Term dS = mThreeValuedAuxVarGen.getDefineGuard(q0);
			final Term ndS = mThreeValuedAuxVarGen.getNonDefineGuard(q0);
			//normal labels
			final Term uR = mThreeValuedAuxVarGen.getUseGuard(R);
			final Term nuR = SmtUtils.not(mScript, uR);
			final Term RandS = SmtUtils.and(mScript, R, S);
			final Term notR = SmtUtils.not(mScript, R);
			final Term notRandS = SmtUtils.and(mScript, notR, S);
			
			q0.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, uR, notR, ndS)));
			q0.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, uR, R, ndS)));
			q1.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, uR, RandS , dS)));
			q1.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, uR, notRandS , dS)));
			
			q0.connectOutgoing(qw, new TimedLabel(SmtUtils.and(mScript, nuR, ndS)));
			q1.connectOutgoing(qw, new TimedLabel(SmtUtils.and(mScript, nuR, dS, S)));
			qw.connectOutgoing(qw, new TimedLabel(SmtUtils.and(mScript, nuR, ndS)));
			qw.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, uR, notR, ndS)));
			qw.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, uR, R, ndS)));
			
			return q0;		
		} else {
			throw new RuntimeException("Scope not implemented");
		}
	}
	
	
}
