package de.uni_freiburg.informatik.ultimate.reqtotest.req;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeAfter;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeGlob;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.BndDelayedResponsePatternUT;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.BndInvariancePattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.BndResponsePatternTT;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.BndResponsePatternTU;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.BndResponsePatternUT;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InitializationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InstAbsPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InvariantPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.TogglePatternDelayed;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.UniversalityPattern;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.pea2boogie.CddToSmt;
import de.uni_freiburg.informatik.ultimate.reqtotest.graphtransformer.AuxVarGen;

public class ReqToGraph {
	
	private final ILogger mLogger;
	
	private final CddToSmt mCddToSmt;
	private final Req2TestReqSymbolTable mReqSymbolTable;

	private final AuxVarGen mThreeValuedAuxVarGen;
	private final Script mScript;
	private final Term mSmtTrue;
	
	// set if the universality pattern sets define flags or not (true: unsound but helpful, false: sound but often no tests found)
	private final boolean UNIVERSALITY_IS_DEFINITNG = false;
	
	public ReqToGraph(final ILogger logger, AuxVarGen threeValuedAuxVarGen, Script script, CddToSmt cddToSmt,
			Req2TestReqSymbolTable reqSymbolTable){
		mLogger = logger;
		mThreeValuedAuxVarGen = threeValuedAuxVarGen;
		mCddToSmt = cddToSmt;
		mScript = script;
		mReqSymbolTable = reqSymbolTable;
		mSmtTrue = mScript.term("true");
	}

	
	public List<ReqGuardGraph> patternListToBuechi(List<PatternType> patternList){
		final List<ReqGuardGraph> gs = new ArrayList<ReqGuardGraph>();
		for (PatternType pattern: patternList) {
			if (! (pattern instanceof InitializationPattern)){
				ReqGuardGraph aut = patternToTestAutomaton(pattern);
				if(aut != null) {
					gs.add(aut);
				}
			}
		}
		return gs;
	}
	
	private Term getDurationTerm(String duration) {
		if (mReqSymbolTable.isConstVar(duration)) {
			return mScript.variable(duration, mScript.sort("Int"));
		} else {
			return mScript.numeral(duration);
		}
	}
	
	 
	/*								  Global		After		Until		After Until
	    BndInvariancePattern			X
    	BndResponsePatternTT			X
    	BndResponsePatternUT			X
       	BndResponsePatternTU 			X
       	BndDelayedResponsePatternUT
    	InvariantPattern				X
    	InstAbsPattern					X
      	UniversalityPattern				X
      	TogglePatternDelayed			X
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
		} else if(pattern instanceof BndDelayedResponsePatternUT){
			return getBndDelayedResponsePatternUT(pattern);
		} else if (pattern instanceof InstAbsPattern){
			return getInstAbsPattern(pattern);
		} else if(pattern instanceof BndResponsePatternTU){
			return getBndResponsePatternTUPattern(pattern);
		} else if(pattern instanceof TogglePatternDelayed){
			return getTogglePatternDelayed(pattern);
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
			String id = pattern.getId();
			final ReqGuardGraph q0 = new ReqGuardGraph(0,id);
			final ReqGuardGraph q1 = new ReqGuardGraph(1,id);
			final ReqGuardGraph q2 = new ReqGuardGraph(2,id);
			final ReqGuardGraph qw = new ReqGuardGraph(-1,id);
			//create effect guards

			mThreeValuedAuxVarGen.setEffectLabel(q0, S);
			final String durationTrigger = pattern.getDuration().get(0);
			final String durationEffect = pattern.getDuration().get(1);
			TermVariable clockIdent = mThreeValuedAuxVarGen.generateClockIdent(q0);
			//assuming RT-Consistency <>(\leq t) can be transformed into <>(==t)
			Term triggerLess = SmtUtils.less(mScript, clockIdent, getDurationTerm(durationTrigger));
			Term triggerEq = SmtUtils.binaryEquality(mScript, clockIdent, getDurationTerm(durationTrigger));	
			Term effectLess = SmtUtils.less(mScript, clockIdent, getDurationTerm(durationEffect));
			Term effectEq = SmtUtils.binaryEquality(mScript, clockIdent, getDurationTerm(durationEffect));
					//define labels 
			final Term dS = mThreeValuedAuxVarGen.getDefineGuard(q0);
			final Term ndS = mThreeValuedAuxVarGen.getNonDefineGuard(q0);
			//normal labels
			final Term uR = mThreeValuedAuxVarGen.getUseGuard(R);
			final Term nuR = SmtUtils.not(mScript, uR); 
			final Term nR = SmtUtils.not(mScript, R);
			
			q0.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, ndS, uR, nR), mSmtTrue ));
			q0.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, uR, R, ndS), mSmtTrue, clockIdent));
			q1.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, uR, R, ndS), triggerLess));
			q1.connectOutgoing(q2, new TimedLabel(SmtUtils.and(mScript, uR, R), triggerEq, clockIdent));
			q2.connectOutgoing(q2, new TimedLabel(SmtUtils.and(mScript,  dS, S), effectLess, true));
			q2.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript,  dS, S), effectEq, true));
			
			q0.connectOutgoing(qw, new TimedLabel(SmtUtils.and(mScript, nuR, ndS), mSmtTrue));
			qw.connectOutgoing(qw, new TimedLabel(SmtUtils.and(mScript, nuR, ndS), mSmtTrue));
			qw.connectOutgoing(q0, new TimedLabel(SmtUtils.or(mScript, uR, nR, ndS), mSmtTrue));
			qw.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, uR, R, ndS), mSmtTrue, clockIdent));
			
			return q0;		
		} else {
			scopeNotImplementedWarning(pattern);
			return null;
		}
	}
	
	/*
"{scope}, it is always the case that if "R" holds, then "S" holds after at most "c1" time units for at least "c2"
 * time units
	 */
	private ReqGuardGraph getBndDelayedResponsePatternUT(PatternType pattern){
		if(pattern.getScope() instanceof SrParseScopeGlob) {
			final List<CDD> args = pattern.getCdds();
			final Term R = mCddToSmt.toSmt(args.get(1));
			final Term S = mCddToSmt.toSmt(args.get(0)); 
			//create states to identify automaton
			String id = pattern.getId();
			final ReqGuardGraph q0 = new ReqGuardGraph(0,id);
			final ReqGuardGraph q1 = new ReqGuardGraph(1,id);
			final ReqGuardGraph q2 = new ReqGuardGraph(2,id);
			//create effect guards

			mThreeValuedAuxVarGen.setEffectLabel(q0, S);
			final String delayEffect = pattern.getDuration().get(0);
			final String durationEffect = pattern.getDuration().get(1);
			TermVariable clockIdent = mThreeValuedAuxVarGen.generateClockIdent(q0);
			//assuming RT-Consistency <>(\leq t) can be transformed into <>(==t)
			Term triggerLess = SmtUtils.less(mScript, clockIdent, getDurationTerm(delayEffect));
			Term triggerEq = SmtUtils.binaryEquality(mScript, clockIdent, getDurationTerm(delayEffect));	
			Term effectLess = SmtUtils.less(mScript, clockIdent, getDurationTerm(durationEffect));
			Term effectEq = SmtUtils.binaryEquality(mScript, clockIdent, getDurationTerm(durationEffect));
			//define labels 
			final Term dS = mThreeValuedAuxVarGen.getDefineGuard(q0);
			final Term ndS = mThreeValuedAuxVarGen.getNonDefineGuard(q0);
			//normal labels
			final Term uR = mThreeValuedAuxVarGen.getUseGuard(R);
			final Term nuR = SmtUtils.not(mScript, uR); 
			final Term nR = SmtUtils.not(mScript, R);
			
			q0.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, ndS, uR, nR), mSmtTrue));
			q0.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, ndS, nuR), mSmtTrue));
			q0.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, uR, R, ndS), mSmtTrue, clockIdent));
			q1.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, uR, R, ndS), triggerLess));
			q1.connectOutgoing(q2, new TimedLabel(SmtUtils.and(mScript, uR, R), triggerEq, clockIdent));
			q2.connectOutgoing(q2, new TimedLabel(SmtUtils.and(mScript,  dS, S), effectLess, true));
			q2.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript,  dS, S), effectEq, true));
			
			return q0;		
		} else {
			scopeNotImplementedWarning(pattern);
			return null;
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
			String id = pattern.getId();
			final ReqGuardGraph q0 = new ReqGuardGraph(0, id);
			final ReqGuardGraph q1 = new ReqGuardGraph(1, id);
			final ReqGuardGraph q2 = new ReqGuardGraph(2, id);
			final ReqGuardGraph qw = new ReqGuardGraph(-1, id);
			//create effect guards
			mThreeValuedAuxVarGen.setEffectLabel(q0, S);
			final String duration = pattern.getDuration().get(0);
			TermVariable clockIdent = mThreeValuedAuxVarGen.generateClockIdent(q0);
			//assuming RT-Consistency <>(\leq t) can be transformed into <>(==t)
			Term triggerLess = SmtUtils.less(mScript, clockIdent, getDurationTerm(duration));
			Term triggerEq = SmtUtils.binaryEquality(mScript, clockIdent, getDurationTerm(duration));	
					//define labels 
			final Term dS = mThreeValuedAuxVarGen.getDefineGuard(q0);
			final Term ndS = mThreeValuedAuxVarGen.getNonDefineGuard(q0);
			//normal labels
			final Term uR = mThreeValuedAuxVarGen.getUseGuard(R);
			final Term nuR = SmtUtils.not(mScript, uR); 
			final Term nR = SmtUtils.not(mScript, R);
			
			q0.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, ndS, uR, nR), mSmtTrue));
			q0.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, uR, R, ndS), mSmtTrue, clockIdent));
			q1.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, uR, R, ndS), triggerLess));
			q1.connectOutgoing(q2, new TimedLabel(SmtUtils.and(mScript, uR, R, ndS), triggerEq));
			q1.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, nR, uR, ndS), triggerLess));
			q2.connectOutgoing(q2, new TimedLabel(SmtUtils.and(mScript,  uR, R, dS, S), mSmtTrue, true));
			q2.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript,  nR, uR, S, dS), mSmtTrue, true));
			
			q0.connectOutgoing(qw, new TimedLabel(SmtUtils.and(mScript, nuR, ndS), mSmtTrue));
			q1.connectOutgoing(qw, new TimedLabel(SmtUtils.and(mScript, nuR, ndS), mSmtTrue));
			qw.connectOutgoing(qw, new TimedLabel(SmtUtils.and(mScript, nuR, ndS), mSmtTrue));
			qw.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, uR, nR, ndS), mSmtTrue));
			qw.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, uR, R, ndS), clockIdent));
			
			
			return q0;		
		} else {
			scopeNotImplementedWarning(pattern);
			return null;
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
			String id = pattern.getId();
			final ReqGuardGraph q0 = new ReqGuardGraph(0, id);
			final ReqGuardGraph q1 = new ReqGuardGraph(1, id);
			final ReqGuardGraph qw = new ReqGuardGraph(-1, id);
			//create effect guards
			mThreeValuedAuxVarGen.setEffectLabel(q0, S);
			final String duration = pattern.getDuration().get(0);
			TermVariable clockIdent = mThreeValuedAuxVarGen.generateClockIdent(q0);
			Term clockGuard = SmtUtils.leq(mScript, clockIdent, getDurationTerm(duration));	
			Term clockGuardGeq = SmtUtils.greater(mScript, clockIdent, getDurationTerm(duration));	
					//define labels 
			final Term dS = mThreeValuedAuxVarGen.getDefineGuard(q0);
			final Term ndS = mThreeValuedAuxVarGen.getNonDefineGuard(q0);
			//normal labels
			final Term uR = mThreeValuedAuxVarGen.getUseGuard(R);
			final Term nuR = SmtUtils.not(mScript, uR); 
			final Term nR = SmtUtils.not(mScript, R);
			
			q0.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, uR, nR, ndS), mSmtTrue));
			q0.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, uR, R, dS, S), mSmtTrue, clockIdent, true));
			q1.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, clockGuard, S, dS, uR, nR), mSmtTrue, true));
			q1.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, clockGuard, S, dS, uR, R), mSmtTrue, clockIdent, true));
			q1.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, clockGuardGeq, uR, nR, ndS), mSmtTrue));
			
			q0.connectOutgoing(qw, new TimedLabel(SmtUtils.and(mScript, nuR, ndS), mSmtTrue));
			qw.connectOutgoing(qw, new TimedLabel(SmtUtils.and(mScript, nuR, ndS), mSmtTrue));
			qw.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, uR, nR, ndS), mSmtTrue));
			qw.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, uR, R, dS, S), mSmtTrue, clockIdent, true));
			
			return q0;	
		} else {
			scopeNotImplementedWarning(pattern);
			return null;
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
			String id = pattern.getId();
			final ReqGuardGraph q0 = new ReqGuardGraph(0, id);
			final ReqGuardGraph q1 = new ReqGuardGraph(1, id);
			final ReqGuardGraph q2 = new ReqGuardGraph(2, id);
			final ReqGuardGraph qw = new ReqGuardGraph(-1, id);
			//create effect guards
			mThreeValuedAuxVarGen.setEffectLabel(q0, S);
			final String duration = pattern.getDuration().get(0);
			TermVariable clockIdent = mThreeValuedAuxVarGen.generateClockIdent(q0);
			//assuming RT-Consistency <>(\leq t) can be transformed into <>(==t)
			Term clockGuardLess = SmtUtils.less(mScript, clockIdent, getDurationTerm(duration));
			Term clockGuardEq = SmtUtils.binaryEquality(mScript, clockIdent, getDurationTerm(duration));	
			Term clockGuardGeq = SmtUtils.geq(mScript, clockIdent, getDurationTerm(duration));
			//define labels 
			final Term dS = mThreeValuedAuxVarGen.getDefineGuard(q0);
			final Term ndS = mThreeValuedAuxVarGen.getNonDefineGuard(q0);
			//normal labels
			final Term uR = mThreeValuedAuxVarGen.getUseGuard(R);
			final Term nuR = SmtUtils.not(mScript, uR); 
			final Term uS = mThreeValuedAuxVarGen.getUseGuard(S);
			final Term nR = SmtUtils.not(mScript, R);
			
			//regular automaton
			q0.connectOutgoing(q0, new TimedLabel( SmtUtils.and(mScript, ndS, uR, nR), mSmtTrue));
			q0.connectOutgoing(q0, new TimedLabel( SmtUtils.and(mScript, ndS, uS, S), mSmtTrue));
			q0.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, uR, R, ndS), mSmtTrue, clockIdent));
			q1.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, R, uR, ndS), clockGuardLess));
			q1.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, nR, uR, ndS), clockGuardGeq));
			q1.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, R, uR, S, dS), clockGuardGeq, true));

			q1.connectOutgoing(q2, new TimedLabel(SmtUtils.and(mScript, ndS, uR, nR),clockGuardLess));
			q1.connectOutgoing(q2, new TimedLabel(SmtUtils.and(mScript, ndS, nuR),clockGuardLess));
			q2.connectOutgoing(q2, new TimedLabel(SmtUtils.and(mScript, ndS), clockGuardLess));
			q2.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, S, dS), clockGuardEq, true));
			// uncertainty
			q0.connectOutgoing(qw, new TimedLabel(SmtUtils.and(mScript, nuR, ndS), mSmtTrue));
			qw.connectOutgoing(qw, new TimedLabel(SmtUtils.and(mScript, nuR, ndS), mSmtTrue));
			qw.connectOutgoing(q0, new TimedLabel(SmtUtils.or(mScript, 
					SmtUtils.and(mScript, uR, nR, ndS),
					SmtUtils.and(mScript, uS, S, ndS)), mSmtTrue));
			qw.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, uR, R, ndS), mSmtTrue, clockIdent));
			
			return q0;		
		} else if(pattern.getScope() instanceof SrParseScopeAfter) {
			final List<CDD> args = pattern.getCdds();
			final Term R = mCddToSmt.toSmt(args.get(1));
			final Term S = mCddToSmt.toSmt(args.get(0)); 
			final Term Q = mCddToSmt.toSmt(pattern.getScope().getCdd1()); 
			//create states to identify automaton
			String id = pattern.getId();
			final ReqGuardGraph q0 = new ReqGuardGraph(0, id); 
			final ReqGuardGraph q1 = new ReqGuardGraph(1, id);
			final ReqGuardGraph q2 = new ReqGuardGraph(2, id);
			final ReqGuardGraph q3 = new ReqGuardGraph(3, id);
			final ReqGuardGraph qw = new ReqGuardGraph(-1, id);
			//create effect guards
			mThreeValuedAuxVarGen.setEffectLabel(q1, S);
			final String duration = pattern.getDuration().get(0);
			TermVariable clockIdent = mThreeValuedAuxVarGen.generateClockIdent(q0);
			//assuming RT-Consistency <>(\leq t) can be transformed into <>(==t)
			Term clockGuardLess = SmtUtils.less(mScript, clockIdent, getDurationTerm(duration));
			Term clockGuardEq = SmtUtils.binaryEquality(mScript, clockIdent, getDurationTerm(duration));	
			Term clockGuardGeq = SmtUtils.geq(mScript, clockIdent, getDurationTerm(duration));
			//define labels 
			final Term dS = mThreeValuedAuxVarGen.getDefineGuard(q1);
			final Term ndS = mThreeValuedAuxVarGen.getNonDefineGuard(q1);
			//normal labels
			final Term uR = mThreeValuedAuxVarGen.getUseGuard(R);
			final Term nuR = SmtUtils.not(mScript, uR); 
			final Term uS = mThreeValuedAuxVarGen.getUseGuard(S);
			final Term nR = SmtUtils.not(mScript, R);
			final Term nQ = SmtUtils.not(mScript, Q);
			final Term uQ = mThreeValuedAuxVarGen.getUseGuard(Q);
			final Term nuQ = SmtUtils.not(mScript, Q);
			
			q0.connectOutgoing(q1, new TimedLabel( SmtUtils.and(mScript, ndS, uQ, Q), mSmtTrue));
			q0.connectOutgoing(q2, new TimedLabel( SmtUtils.and(mScript, ndS, uQ, Q, R, uR), mSmtTrue));
			q0.connectOutgoing(q0, new TimedLabel( SmtUtils.and(mScript, ndS, 
					SmtUtils.or(mScript, nQ, nuQ)), mSmtTrue));
			//regular automaton
			q1.connectOutgoing(q1, new TimedLabel( SmtUtils.and(mScript, ndS, uR, nR), mSmtTrue));
			q1.connectOutgoing(q1, new TimedLabel( SmtUtils.and(mScript, ndS, uS, S), mSmtTrue));
			q1.connectOutgoing(q2, new TimedLabel(SmtUtils.and(mScript, uR, R, ndS), mSmtTrue, clockIdent));
			q2.connectOutgoing(q2, new TimedLabel(SmtUtils.and(mScript, R, uR, ndS), clockGuardLess));
			q2.connectOutgoing(q2, new TimedLabel(SmtUtils.and(mScript, nR, uR, ndS), clockGuardGeq));
			q2.connectOutgoing(q2, new TimedLabel(SmtUtils.and(mScript, R, uR, S, dS), clockGuardGeq, true));

			q2.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, ndS, uR, nR),clockGuardLess));
			q2.connectOutgoing(q3, new TimedLabel(SmtUtils.and(mScript, ndS, nuR),clockGuardLess));
			q3.connectOutgoing(q3, new TimedLabel(SmtUtils.and(mScript, ndS), clockGuardLess));
			q3.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, S, dS), clockGuardEq, true));
			// uncertainty
			q1.connectOutgoing(qw, new TimedLabel(SmtUtils.and(mScript, nuR, ndS), mSmtTrue));
			qw.connectOutgoing(qw, new TimedLabel(SmtUtils.and(mScript, nuR, ndS), mSmtTrue));
			qw.connectOutgoing(q1, new TimedLabel(SmtUtils.or(mScript, 
					SmtUtils.and(mScript, uR, nR, ndS),
					SmtUtils.and(mScript, uS, S, ndS)), mSmtTrue));
			qw.connectOutgoing(q2, new TimedLabel(SmtUtils.and(mScript, uR, R, ndS), mSmtTrue, clockIdent));
			
			return q0;		
		} else {
			scopeNotImplementedWarning(pattern);
			return null;
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
			String id = pattern.getId();
			final ReqGuardGraph q0 = new ReqGuardGraph(0, id);
			mThreeValuedAuxVarGen.setEffectLabel(q0, S);
			//define labels 
			final Term dS = mThreeValuedAuxVarGen.getDefineGuard(q0);
			final Term ndS = mThreeValuedAuxVarGen.getNonDefineGuard(q0);
			//normal labels
			final Term uR = mThreeValuedAuxVarGen.getUseGuard(R);
			final Term nuR = SmtUtils.not(mScript, uR); 
			final Term uS = mThreeValuedAuxVarGen.getUseGuard(S);
			final Term nR = SmtUtils.not(mScript, R);
			q0.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, nuR, ndS), mSmtTrue));
			q0.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, uR, nR, ndS), mSmtTrue));
			q0.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, S, uS, ndS), mSmtTrue));
			q0.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, uR, R, dS, S), mSmtTrue,true));
			return q0;
		} else if(pattern.getScope() instanceof SrParseScopeAfter) {
			final List<CDD> args = pattern.getCdds();
			final Term R = mCddToSmt.toSmt(args.get(1));
			final Term S = mCddToSmt.toSmt(args.get(0)); 
			final Term Q = mCddToSmt.toSmt(pattern.getScope().getCdd1()); 
			String id = pattern.getId();
			final ReqGuardGraph q0 = new ReqGuardGraph(0, id);
			final ReqGuardGraph q1 = new ReqGuardGraph(1, id);
			mThreeValuedAuxVarGen.setEffectLabel(q0, S);
			//define labels 
			final Term dS = mThreeValuedAuxVarGen.getDefineGuard(q0);
			final Term ndS = mThreeValuedAuxVarGen.getNonDefineGuard(q0);
			//normal labels
			final Term uR = mThreeValuedAuxVarGen.getUseGuard(R);
			final Term nuR = SmtUtils.not(mScript, uR); 
			final Term uS = mThreeValuedAuxVarGen.getUseGuard(S);
			final Term nR = SmtUtils.not(mScript, R);
			final Term uQ = mThreeValuedAuxVarGen.getUseGuard(Q);
			final Term nuQ = SmtUtils.not(mScript, uQ);
			final Term nQ = SmtUtils.not(mScript, Q);
			q0.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, uQ, Q), mSmtTrue));
			q0.connectOutgoing(q0, new TimedLabel(SmtUtils.or(mScript, nuQ, SmtUtils.and(mScript, uQ, nQ)), mSmtTrue));
			q1.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, nuR, ndS), mSmtTrue));
			q1.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, uR, nR, ndS), mSmtTrue));
			q1.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, S, uS, ndS), mSmtTrue));
			q1.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, uR, R, dS, S), mSmtTrue,true));
				return q0;
		} else {
			scopeNotImplementedWarning(pattern);
			return null;
		}
	}
	
	/*
	 *  * {scope}, it is always the case that if "S" holds.
	 */
	private ReqGuardGraph getUniversalityPattern(PatternType pattern){
		if(pattern.getScope() instanceof SrParseScopeGlob) {
			final List<CDD> args = pattern.getCdds();
			final Term S = mCddToSmt.toSmt(args.get(0)); 
			String id = pattern.getId();
			final ReqGuardGraph q0 = new ReqGuardGraph(0, id);
			if (UNIVERSALITY_IS_DEFINITNG) {
				mThreeValuedAuxVarGen.setEffectLabel(q0, S);
				final Term dS = mThreeValuedAuxVarGen.getDefineGuard(q0);
				q0.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, S, dS), mSmtTrue, true));
			} else {
				q0.connectOutgoing(q0, new TimedLabel(S, mSmtTrue));
			}
			return q0;
		} else {
			scopeNotImplementedWarning(pattern);
			return null;
		}
	}
	
	/*
	 *  * {scope}, it is never the case that if "S" holds.
	 */
	private ReqGuardGraph getInstAbsPattern(PatternType pattern){
		if(pattern.getScope() instanceof SrParseScopeGlob) {
			final List<CDD> args = pattern.getCdds();
			final Term S = mCddToSmt.toSmt(args.get(0)); 
			String id = pattern.getId();
			final ReqGuardGraph q0 = new ReqGuardGraph(0, id);
			mThreeValuedAuxVarGen.setEffectLabel(q0, S);
			//define labels 
			final Term dS = mThreeValuedAuxVarGen.getDefineGuard(q0);
			//normal labels
			final Term nS = SmtUtils.not(mScript, S);
			q0.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, nS, dS), mSmtTrue, true));
			return q0;
		} else {
			scopeNotImplementedWarning(pattern);
			return null;
		}
	}
	
	/*	This pattern is for discrete Step LTL
	 *  * {scope}, it is always the case that if "R" holds, then "S" holds in the next Step.
	 */
	@SuppressWarnings("unused")
	private ReqGuardGraph getImmediateResponsePatternToAutomaton(PatternType pattern){
		if(pattern.getScope() instanceof SrParseScopeGlob) {
			final List<CDD> args = pattern.getCdds();
			String id = pattern.getId();
			final Term R = mCddToSmt.toSmt(args.get(1));
			final Term S = mCddToSmt.toSmt(args.get(0)); 
			//create states to identify automaton
			final ReqGuardGraph q0 = new ReqGuardGraph(0, id);
			final ReqGuardGraph q1 = new ReqGuardGraph(1, id);
			final ReqGuardGraph qw = new ReqGuardGraph(-1, id);
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
			
			q0.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, uR, notR, ndS), mSmtTrue));
			q0.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, uR, R, ndS), mSmtTrue));
			q1.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, uR, RandS , dS), mSmtTrue, true));
			q1.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, uR, notRandS , dS), mSmtTrue, true));
			
			q0.connectOutgoing(qw, new TimedLabel(SmtUtils.and(mScript, nuR, ndS), mSmtTrue));
			q1.connectOutgoing(qw, new TimedLabel(SmtUtils.and(mScript, nuR, dS, S), mSmtTrue, true));
			qw.connectOutgoing(qw, new TimedLabel(SmtUtils.and(mScript, nuR, ndS), mSmtTrue));
			qw.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, uR, notR, ndS), mSmtTrue));
			qw.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, uR, R, ndS), mSmtTrue));
			
			return q0;		
		} else {
			scopeNotImplementedWarning(pattern);
			return null;
		}
	}
	
	/*
	 *  * "{scope}, it is always the case that if P holds then S toggles T at most c1 time units later."
	 */
	private ReqGuardGraph getTogglePatternDelayed(PatternType pattern){
		if(pattern.getScope() instanceof SrParseScopeGlob) {
			final List<CDD> args = pattern.getCdds();
			final Term P = mCddToSmt.toSmt(args.get(0)); 
			final Term S = mCddToSmt.toSmt(args.get(1));
			final Term T = mCddToSmt.toSmt(args.get(2));
			String id = pattern.getId();
			final ReqGuardGraph q0 = new ReqGuardGraph(0, id);
			final ReqGuardGraph q1 = new ReqGuardGraph(1, id);
			final ReqGuardGraph q2 = new ReqGuardGraph(2, id);
			final ReqGuardGraph q3 = new ReqGuardGraph(3, id);
			mThreeValuedAuxVarGen.setEffectLabel(q0, T);
			//define labels 
			final Term dT = mThreeValuedAuxVarGen.getDefineGuard(q0);
			final Term ndT = mThreeValuedAuxVarGen.getNonDefineGuard(q0);
			//normal labels
			final Term uP = mThreeValuedAuxVarGen.getUseGuard(P);
			final Term uS = mThreeValuedAuxVarGen.getUseGuard(S);
			final Term nP = SmtUtils.not(mScript, P);
			final Term nS = SmtUtils.not(mScript, S);
			final String duration = pattern.getDuration().get(0);
			TermVariable clockIdent = mThreeValuedAuxVarGen.generateClockIdent(q0);
			Term clockGuardLess = SmtUtils.less(mScript, clockIdent, getDurationTerm(duration));	
			Term clockGuardEq = SmtUtils.binaryEquality(mScript, clockIdent, getDurationTerm(duration));	
			Term clockGuardGeq = SmtUtils.geq(mScript, clockIdent, getDurationTerm(duration));
			//edges
			q0.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, ndT, uP, nP), mSmtTrue));
			q0.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, ndT, nS, uS), mSmtTrue));
			q0.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, P, S, uP, uS, ndT), mSmtTrue));
			q1.connectOutgoing(q1, new TimedLabel(SmtUtils.and(mScript, S, uS, ndT), mSmtTrue));
			q1.connectOutgoing(q2, new TimedLabel(SmtUtils.and(mScript, uS, nS, ndT), mSmtTrue, clockIdent));
			q2.connectOutgoing(q2, new TimedLabel(SmtUtils.and(mScript, uS, nS, ndT), clockGuardLess));
			q2.connectOutgoing(q3, new TimedLabel(SmtUtils.and(mScript, uS, nS, dT, T), clockGuardEq, true));
			q3.connectOutgoing(q3, new TimedLabel(SmtUtils.and(mScript, uS, nS, dT, T), mSmtTrue, true));
			q3.connectOutgoing(q0, new TimedLabel(SmtUtils.and(mScript, S, uS, dT, T), clockGuardGeq, true));
			//no uncertainty here, either we may stay in q0 (by nP or nS) or it is possible to loose track of state changes
			return q0; 

		} else {
			scopeNotImplementedWarning(pattern);
			return null;
		}
	}
	
	private void scopeNotImplementedWarning(PatternType pattern) {
		StringBuilder sb = new StringBuilder();
		sb.append("Scope not implemented: ");
		sb.append(pattern.getScope().toString());
		sb.append(" [in: ");
		sb.append(pattern.getId());
		sb.append(" ]");
		mLogger.warn(sb.toString());
	}
	
	
}
