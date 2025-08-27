package de.uni_freiburg.informatik.ultimate.pea2boogie.generator;

import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace.DCPhase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType.ReqPeas;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.pea2boogie.CddToSmt;
import de.uni_freiburg.informatik.ultimate.pea2boogie.preferences.Pea2BoogiePreferences;

public class RTInconsistencyPreCheck {
	public boolean mDebugReasonCOunter = true;
	public int[] reasonCounter = new int[4];
	
	public boolean mFullSet;

	private Script mScript;
	private ManagedScript mManagedScript;
	private ILogger mLogger;
	private CddToSmt mCddToSmt;
	private IUltimateServiceProvider mServices;
	public int mCombinationNum;
	public Term mDebugTerm;
	public TermVariable mDebugVar;
	public List<ReqsWithAttributes> mListChainLinkReqs = new ArrayList<>();
	public Map<TermVariable, List<ReqsWithAttributes>> mDictVar = new HashMap<>();

	public List<Entry<PatternType<?>, PhaseEventAutomata>[]> mRTIReturnSet;
	public List<List<ReqsWithAttributes>> mRTICombinations = new ArrayList<>();
	public Map<ReqsWithAttributes, List<ReqsWithAttributes>> mChainLinkSingles = new HashMap<>();
	

	public class ReqsWithAttributes {
		public String mName;
		public Phase mPenultimatePhase;
		public Phase mMaxPhase;
		public Phase mBeforeMaxPhase;
		public ReqPeas mOriginalPea;
		public PhaseEventAutomata mOriginalPeaEventAutomata;
		public Term mFullExitCondition;
		public List<Term> mExitConditions;
		public boolean mChainLinkReq;
		public CounterTrace mCounterTrace;

		public ReqsWithAttributes(final ReqPeas reqPea) {
			mOriginalPea = reqPea;
			mChainLinkReq = false;
		}

		public String getName() {
			return mName;

		}

	}

	public class Phase {
		DCPhase mDCPhase;
		Term mInvariant;
		TermVariable[] mInvariantVar;
		Term mBound;

		public Phase(final DCPhase dcPhase) {
			mDCPhase = dcPhase;

		}

	}

	public List<Entry<PatternType<?>, PhaseEventAutomata>[]> doRtiPreCheck(final List<ReqPeas> reqPeas,
			final ILogger logger, final Script script, final CddToSmt cddToSmt, final IUltimateServiceProvider services,
			final ManagedScript managedScript, final int range, boolean preCheckFullSet) {
		mScript = script;
		mManagedScript = managedScript;
		mLogger = logger;
		mCddToSmt = cddToSmt;
		mServices = services;
		mRTIReturnSet = new ArrayList<>();
		mCombinationNum = range;

		mDebugTerm = null;
		mDebugVar = null;
		
		mFullSet = preCheckFullSet;


		getDebugTerm();

		getAttribtes(reqPeas);
		findSinglesForChains();
		if (mFullSet) {
			mCombinationNum = this.mListChainLinkReqs.size();
		}
		rtiCheckSingles();
		rtiCheckChainLinkReqs();

		mLogger.info("RTI PreCheck found " + mRTIReturnSet.size() + " sets");
		for (final Entry<PatternType<?>, PhaseEventAutomata>[] entry : mRTIReturnSet) {
			final StringBuilder sb = new StringBuilder();
			sb.append("[");
			for (final Entry<PatternType<?>, PhaseEventAutomata> e : entry) {
				sb.append(e.getValue().getName() + " ");
			}
			sb.append("]");
			mLogger.info(sb.toString());
		}
		return mRTIReturnSet;

	}

	private void findSinglesForChains() {
		for (final ReqsWithAttributes req : mListChainLinkReqs) {
			mChainLinkSingles.put(req, new ArrayList<>());
			final TermVariable[] variables = req.mFullExitCondition.getFreeVars();
			for (final TermVariable var : variables) {
				final List<ReqsWithAttributes> potentialReqs = mDictVar.get(var);
				if (potentialReqs != null) {
					for (final ReqsWithAttributes otherReq : potentialReqs) {
						if (ChainLinkTest(req, otherReq)) {
							mChainLinkSingles.get(req).add(otherReq);

						}
					}
				}

			}

		}

	}
	
	private boolean ChainLinkTest(final ReqsWithAttributes req1, final ReqsWithAttributes req2) {
		if (!habenSchnittmenge(req1.mFullExitCondition.getFreeVars(), req2.mFullExitCondition.getFreeVars())) {
			return false; // Überschneidung gefunden
		}

		if (((req1.mBeforeMaxPhase != null && req2.mBeforeMaxPhase != null)
				&& req1.mPenultimatePhase.mBound.equals(req2.mPenultimatePhase.mBound))
				&& (req1.mPenultimatePhase.mBound == req2.mPenultimatePhase.mBound)) {

			final Term conjunction =
					SmtUtils.and(mScript, req1.mBeforeMaxPhase.mInvariant, req2.mBeforeMaxPhase.mInvariant);
			final LBool result = SmtUtils.checkSatTerm(mScript, conjunction);
			if (result == LBool.UNSAT) {
				

				return false; // Exit conditions are not disjoint

			}
		}

		return true;
	}
	
	public static <T> boolean habenSchnittmenge(final TermVariable[] vars1, final TermVariable[] variables) {
		for (final TermVariable elem : variables) {
			if (Arrays.asList(vars1).contains(elem)) {
				return true; // Überschneidung gefunden
			}
		}
		return false; // Keine gemeinsamen Elemente
	}

	private void rtiCheckChainLinkReqs() {
		if (mCombinationNum > 0) {
			for (int depth = 1; depth <= mCombinationNum; depth++) {
				mLogger.info("--------------DEPTH (number of chain links) " + depth + "------------------");


				for(int i = 0; i< mListChainLinkReqs.size(); i++) {
					float progress = (i*100)/mListChainLinkReqs.size();
					mLogger.info("STATUS: for depth" + depth + " outOf " + mCombinationNum + "Progress: " + progress + "%");
					
					List<ReqsWithAttributes> chainLinkRes = new ArrayList();
					chainLinkRes.add(mListChainLinkReqs.get(i));
		            
						addChainLinkRecursive(chainLinkRes, depth, this.mListChainLinkReqs.get(i).mExitConditions, 
								new ArrayList<>(this.mListChainLinkReqs.subList(i+1, mListChainLinkReqs.size())));
					


                }
				
				
			}

		}

	}

	private void addChainLinkRecursive( List<ReqsWithAttributes> chainLinkRes, int depth, List<Term> exitConditions, List<ReqsWithAttributes> remainingChainLinks) {
		//Case more chain Links have to be added
		if (depth > chainLinkRes.size()) {
			mLogger.debug("add chain link, remaining chain links: " + remainingChainLinks.size());
			if (remainingChainLinks.isEmpty()) {
				mLogger.debug("No remaining chain links");
				return;
			}
			for (int i = 0; i < remainingChainLinks.size(); i++) {
				for(Term ec: exitConditions) {
					for (Term ecNew : remainingChainLinks.get(i).mExitConditions) {
						Term conjunction = SmtUtils.and(mScript, ec, ecNew);
						if (LBool.SAT != SmtUtils.checkSatTerm(mScript, conjunction)) {
							mLogger.debug("Chain link added");
							List<ReqsWithAttributes> newChainLinkRes = new ArrayList<>(chainLinkRes);
							newChainLinkRes.add(remainingChainLinks.get(i));
							List<Term> newExitConditions = new ArrayList<>();
							for (Term exitCond : exitConditions) {
								if(exitCond != ec) {
									newExitConditions.add(exitCond);
								}
							}
							for (Term exitCond : remainingChainLinks.get(i).mExitConditions) {
								if (exitCond != ecNew) {
									newExitConditions.add(exitCond);
								}
							}
							if(remainingChainLinks.size() > i+1) {
								addChainLinkRecursive(newChainLinkRes, depth, newExitConditions,
										new ArrayList<>(remainingChainLinks.subList(i+1, remainingChainLinks.size())));
							}

						}
					}
				}
				
			}
		}
		//Case number of chainlinks reached
		else if (depth == chainLinkRes.size()) {
			findSinglesForChains(chainLinkRes, exitConditions);
			
		}
		
	}

	private void findSinglesForChains(List<ReqsWithAttributes> chainLinkRes, List<Term> exitConditions) {

		mLogger.warn("Finding singles for chain link requirements: " );
		for (ReqsWithAttributes r : chainLinkRes) {
			mLogger.info("   " + r.mName);
		}
		
		List<ReqsWithAttributes> potentialSingles = new ArrayList();
		if (chainLinkRes.size() == 1) {
			potentialSingles = mChainLinkSingles.get(chainLinkRes.get(0));
		} else {
			for (ReqsWithAttributes req : chainLinkRes) {
				potentialSingles.addAll(mChainLinkSingles.get(req));
				/*
				for(int i = 1;  i < chainLinkRes.size(); i++) {
					if(mChainLinkSingles.get(chainLinkRes.get(i)).contains(req)) {
                       break;
                    }
				}
				for (Term exitCond : exitConditions) {
					if(habenSchnittmenge(exitCond.getFreeVars(), req.mFullExitCondition.getFreeVars() )){
						potentialSingles.add(req);
					}
				}
				*/
			}
		}
		if (potentialSingles.isEmpty()) {
			mLogger.debug("No potential singles found");
			return;
		}
		mLogger.debug("Potential singles found: " + potentialSingles.size());
		fillWithSinglesRecursive(potentialSingles, chainLinkRes, exitConditions, new ArrayList());
		
		
	}

	private void fillWithSinglesRecursive(List<ReqsWithAttributes> potentialSingles,
			List<ReqsWithAttributes> chainLinkRes, List<Term> exitConditions, List<ReqsWithAttributes> usedSingles) {
		mLogger.debug("add single, potential singles left: " + potentialSingles.size());
		for (int i = 0; i< potentialSingles.size(); i++) {

			List<ReqsWithAttributes> newUsedSingles = new ArrayList<>(usedSingles);
			List<Term> reducedExitConditions = new ArrayList<>();
			for(Term exitCon: exitConditions) {
				Term conjunction = SmtUtils.and(mScript, exitCon, potentialSingles.get(i).mFullExitCondition);
				if (LBool.SAT == SmtUtils.checkSatTerm(mScript, conjunction)) {
					reducedExitConditions.add(exitCon);
				}
			}
			if(reducedExitConditions.size() == exitConditions.size()) {
				mLogger.debug("No reduction of exit conditions");
				
            } 
			else{
				newUsedSingles.add(potentialSingles.get(i));
			
			
			if (reducedExitConditions.isEmpty()) {
				chainLinkRtiFoundCheck(chainLinkRes, newUsedSingles);
			} else if (reducedExitConditions.size() < exitConditions.size()) {
				mLogger.debug("Reduced exit conditions to " + reducedExitConditions.size());
				fillWithSinglesRecursive(
					    new ArrayList<>(potentialSingles.subList(i, potentialSingles.size())),
					    chainLinkRes,
					    reducedExitConditions, newUsedSingles
					);

			} 
		}
		}

		
	}

	private void chainLinkRtiFoundCheck(List<ReqsWithAttributes> chainLinkRes, List<ReqsWithAttributes> usedSingles) {
		for (List<ReqsWithAttributes> rtiSet : mRTICombinations) {
			boolean allFound = true;
			if(rtiSet.containsAll(usedSingles)) {
				allFound = true;
				
				mLogger.debug("set not minimal");	
				return;
			} 
					
				
			
		}
		mLogger.info("RTI found for chain link reqs: ");
		List<ReqsWithAttributes> fullSet = new ArrayList<>();
		fullSet.addAll(chainLinkRes);
		fullSet.addAll(usedSingles);
		
		Term conjunction = fullSet.get(0).mFullExitCondition;

		for (int i = 1; i < fullSet.size(); i++) {
		    conjunction = SmtUtils.and(mScript, conjunction, fullSet.get(i).mFullExitCondition);
		}

		LBool result = SmtUtils.checkSatTerm(mScript, conjunction);
		if (result != LBool.UNSAT) {
			mLogger.debug("set not disjoint");
			return;
		}
		mRTIReturnSet.add(rtiSetsFormatted(fullSet));
	}

	public void getDebugTerm() {
		// BIG TODO, workaround
		final Logics logic = Logics.QF_UFNIA;
		final Theory theo = new Theory(logic);
		final Term rhs = mScript.decimal(Double.toString(2.0));
		final Sort sort2 = rhs.getSort();
		final Sort sort = theo.getRealSort();
		mDebugVar = theo.createTermVariable("debugVar", sort2);
		final boolean geko = true;
	}



	private void rtiCheckSingles() {
		for (final Entry variablesEntry : mDictVar.entrySet()) {
			final List<List<ReqsWithAttributes>> combinations =
					combinations2((List<ReqsWithAttributes>) variablesEntry.getValue());
			for (final List<ReqsWithAttributes> pair : combinations) {
				final List<ReqsWithAttributes> psorted = new ArrayList<>(pair);
				psorted.sort(Comparator.comparing(ReqsWithAttributes::getName));

				if (mRTICombinations.contains(psorted)) {
					continue; // already checked this combination
				}

				if (rtiCheckFor2Reqs(pair.get(0), pair.get(1))) {
					mLogger.info("RTI found for " + pair.get(0).mName + " and " + pair.get(1).mName);
					mRTIReturnSet.add(rtiSetsFormatted(pair));
				}
			}

		}
		// TODO Auto-generated method stub

	}

	private boolean rtiCheckFor2Reqs(final ReqsWithAttributes reqsWithAttributes,
			final ReqsWithAttributes reqsWithAttributes2) {

		boolean help = true;

		Term conjunction =
				SmtUtils.and(mScript, reqsWithAttributes.mFullExitCondition, reqsWithAttributes2.mFullExitCondition);
		LBool result = SmtUtils.checkSatTerm(mScript, conjunction);
		if (result != LBool.UNSAT) {

			if (mDebugReasonCOunter) {
				help = false;
				reasonCounter[0]++;
			} else {
				return false; // Exit conditions are not disjoint
			}

			// return false;
		}
		if (((reqsWithAttributes.mBeforeMaxPhase != null && reqsWithAttributes2.mBeforeMaxPhase != null)
				&& reqsWithAttributes.mPenultimatePhase.mBound.equals(reqsWithAttributes2.mPenultimatePhase.mBound))
				&& (reqsWithAttributes.mPenultimatePhase.mBound == reqsWithAttributes2.mPenultimatePhase.mBound)) {

			conjunction = SmtUtils.and(mScript, reqsWithAttributes.mBeforeMaxPhase.mInvariant,
					reqsWithAttributes2.mBeforeMaxPhase.mInvariant);
			result = SmtUtils.checkSatTerm(mScript, conjunction);
			if (result == LBool.UNSAT) {

				if (mDebugReasonCOunter) {
					help = false;
					reasonCounter[3]++;
				} else {
					return false; // Exit conditions are not disjoint
				}
			}
		}
		mRTICombinations.add(Arrays.asList(reqsWithAttributes, reqsWithAttributes2));
		conjunction = SmtUtils.and(mScript, reqsWithAttributes.mMaxPhase.mInvariant,
				reqsWithAttributes2.mMaxPhase.mInvariant);
		result = SmtUtils.checkSatTerm(mScript, conjunction);
		if (result == LBool.UNSAT) {

			if (mDebugReasonCOunter) {
				help = false;
				reasonCounter[1]++;
			} else {
				return false; // Exit conditions are not disjoint
			}
		}
		/*
		 * if (reqsWithAttributes.mMaxPhase == reqsWithAttributes2.mMaxPhase) { conjunction = SmtUtils.and(mScript,
		 * reqsWithAttributes.mMaxPhase.mBound, reqsWithAttributes2.mMaxPhase.mBound); result =
		 * SmtUtils.checkSatTerm(mScript, conjunction); if (result == LBool.UNSAT) {
		 * mLogger.info("aussportiert wegen MaxPhase Bound"); if (mDebugReasonCOunter) { help = false;
		 * reasonCounter[2]++; } else { return false; // Exit conditions are not disjoint } }
		 *
		 * }
		 */

		// TODO Auto-generated method stub
		if (!help) {
			return false;
		} else {
			return true;
		}

	}

	public static List<List<ReqsWithAttributes>> combinations2(final List<ReqsWithAttributes> args) {
		final List<List<ReqsWithAttributes>> pairs = new ArrayList<>();

		for (int i = 0; i < args.size(); i++) {
			for (int j = i + 1; j < args.size(); j++) {
				pairs.add(Arrays.asList(args.get(i), args.get(j)));
			}
		}

		return pairs;
	}

	private void getAttribtes(final List<ReqPeas> reqPeas) {

		for (final ReqPeas reqPea : reqPeas) {
			for (final Entry<CounterTrace, PhaseEventAutomata> reqChild : reqPea.getCounterTrace2Pea()) {
				final ReqsWithAttributes newReq = new ReqsWithAttributes(reqPea);
				newReq.mName = reqChild.getValue().getName();
				newReq.mOriginalPeaEventAutomata = reqChild.getValue();
				newReq.mCounterTrace = reqChild.getKey();

				// penultimate Phase
				newReq.mPenultimatePhase =
						new Phase(reqChild.getKey().getPhases()[reqChild.getKey().getPhases().length - 2]);
				newReq.mPenultimatePhase.mInvariant = mCddToSmt
						.toSmt(reqChild.getKey().getPhases()[reqChild.getKey().getPhases().length - 2].getInvariant());

				newReq.mPenultimatePhase.mInvariantVar = newReq.mPenultimatePhase.mInvariant.getFreeVars();
				newReq.mPenultimatePhase.mBound = BoundToSmt(newReq.mPenultimatePhase);
				final Term help = SmtUtils.not(mScript, newReq.mPenultimatePhase.mInvariant);
				newReq.mFullExitCondition = SmtUtils.toDnf(mServices, mManagedScript, help);
				newReq.mExitConditions = new ArrayList<>(Arrays.asList( SmtUtils.getDisjuncts(newReq.mFullExitCondition)));
				if (newReq.mExitConditions.size() > 1) {
					newReq.mChainLinkReq = true;
					mListChainLinkReqs.add(newReq);
				} else {
					final TermVariable[] vars = newReq.mPenultimatePhase.mInvariant.getFreeVars();
					for (final TermVariable var : vars) {
						if (!mDictVar.containsKey(var)) {
							mDictVar.put(var, new ArrayList<>());
						}
						mDictVar.get(var).add(newReq);

					}
				}
				// Max Phase bestimmen
				if (newReq.mPenultimatePhase.mDCPhase.getBoundType() != 0) {
					newReq.mMaxPhase =
							new Phase(reqChild.getKey().getPhases()[reqChild.getKey().getPhases().length - 2]);
					if (reqChild.getKey().getPhases().length > 2) {
						newReq.mBeforeMaxPhase =
								new Phase(reqChild.getKey().getPhases()[reqChild.getKey().getPhases().length - 3]);
					}
				} else {
					newReq.mMaxPhase =
							new Phase(reqChild.getKey().getPhases()[reqChild.getKey().getPhases().length - 3]);
					if (reqChild.getKey().getPhases().length > 3) {
						newReq.mBeforeMaxPhase =
								new Phase(reqChild.getKey().getPhases()[reqChild.getKey().getPhases().length - 4]);
					}
				}
				newReq.mMaxPhase.mInvariant = mCddToSmt.toSmt(newReq.mMaxPhase.mDCPhase.getInvariant());
				newReq.mMaxPhase.mInvariantVar = newReq.mMaxPhase.mInvariant.getFreeVars();
				newReq.mMaxPhase.mBound = BoundToSmt(newReq.mMaxPhase);
				if (newReq.mBeforeMaxPhase != null) {
					newReq.mBeforeMaxPhase.mInvariant = mCddToSmt.toSmt(newReq.mBeforeMaxPhase.mDCPhase.getInvariant());
					newReq.mBeforeMaxPhase.mInvariantVar = newReq.mBeforeMaxPhase.mInvariant.getFreeVars();
					newReq.mBeforeMaxPhase.mBound = BoundToSmt(newReq.mBeforeMaxPhase);

				}

			}

		}

	}

	public Entry<PatternType<?>, PhaseEventAutomata>[] rtiSetsFormatted(final List<ReqsWithAttributes> reqs) {
		final List<Map.Entry<PatternType<?>, PhaseEventAutomata>> entryList = new ArrayList<>();
		for (final ReqsWithAttributes req : reqs) {
			final Map.Entry<PatternType<?>, PhaseEventAutomata> entry1 =
					new AbstractMap.SimpleEntry<>(req.mOriginalPea.getPattern(), req.mOriginalPeaEventAutomata);
			entryList.add(entry1);
		}
		final Map.Entry<PatternType<?>, PhaseEventAutomata>[] entryArray = entryList.toArray(new Map.Entry[0]);
		Arrays.sort(entryArray, Comparator.comparing(Map.Entry::getValue));
		return entryArray;
	}

	private Term BoundToSmt(final Phase phase) {
		final Term boundTerm = mScript.term("true");
		if (phase.mDCPhase.getBoundType() == 0) {
			return mScript.term("true");
		} else if (phase.mDCPhase.getBoundType() == 2) {
			final Term rhs = mScript.decimal(Double.toString(phase.mDCPhase.getBound()));
			return SmtUtils.greater(mScript, mDebugVar, rhs);
			// t = SmtUtils.leq(mScript, startTerm, SmtUtils.term("x", phase.mDCPhase.getBound()));
			// return mScript.term("x>" + phase.mDCPhase.getBound());

		} else if (phase.mDCPhase.getBoundType() == 1) {
			final Term rhs = mScript.decimal(Double.toString(phase.mDCPhase.getBound()));
			return SmtUtils.geq(mScript, mDebugVar, rhs);
			// t = SmtUtils.geq(mScript, startTerm, SmtUtils.term("x", phase.mDCPhase.getBound()));
			// return mScript.term("x<" + phase.mDCPhase.getBound());
		} else if (phase.mDCPhase.getBoundType() == -2) {
			final Term rhs = mScript.decimal(Double.toString(phase.mDCPhase.getBound()));
			return SmtUtils.less(mScript, mDebugVar, rhs);
			// t = SmtUtils.eq(mScript, startTerm, SmtUtils.term("x", phase.mDCPhase.getBound()));
			// return mScript.term("x==" + phase.mDCPhase.getBound());
		} else {
			final Term rhs = mScript.decimal(Double.toString(phase.mDCPhase.getBound()));
			return SmtUtils.leq(mScript, mDebugVar, rhs);
		}

	}
}
