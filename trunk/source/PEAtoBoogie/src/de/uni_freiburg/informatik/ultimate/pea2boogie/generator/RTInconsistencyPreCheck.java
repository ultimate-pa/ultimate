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

public class RTInconsistencyPreCheck {
	public boolean mDebugReasonCOunter = true;
	public int[] reasonCounter = new int[4];

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
		public Term[] mExitConditions;
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
			final ManagedScript managedScript, final int range) {
		mScript = script;
		mManagedScript = managedScript;
		mLogger = logger;
		mCddToSmt = cddToSmt;
		mServices = services;
		mRTIReturnSet = new ArrayList<>();
		mCombinationNum = range;

		mDebugTerm = null;
		mDebugVar = null;

		getDebugTerm();

		getAttribtes(reqPeas);
		findSinglesForChains();
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

	private void rtiCheckChainLinkReqs() {
		if (mCombinationNum > 0) {
			for (int counter = 1; counter <= mCombinationNum; counter++) {
				mLogger.info("DEPTH " + counter);

				for (final ReqsWithAttributes req : mListChainLinkReqs) {
					final List<ReqsWithAttributes> testSet = new ArrayList<>();
					testSet.add(req);
					final Term joinedEC = req.mFullExitCondition;
					final int chainLinkCounter = mListChainLinkReqs.indexOf(req);

					addChainLinkRecursive(chainLinkCounter, testSet, joinedEC, counter);

				}
			}

		}

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

	private void addChainLinkRecursive(final int startIdx, final List<ReqsWithAttributes> testSet, final Term joinedEC,
			final int counter) {

		// Basisfälle
		if (testSet.size() == counter) {
			fillwithSingles(testSet, joinedEC);
			return;
		}
		if (testSet.size() > counter) {
			return;
		}

		for (int i = startIdx + 1; i < mListChainLinkReqs.size(); i++) {
			final ReqsWithAttributes req = mListChainLinkReqs.get(i);

			if (ChainLinkTest(testSet.get(0), req)) {

				mLogger.info("adding " + req.mName);

				// wählen
				testSet.add(req);

				// NICHT joinedEC überschreiben; lokale, erweiterte Variante bilden
				final Term nextJoinedEC = SmtUtils.and(mScript, joinedEC, req.mFullExitCondition);

				// weitergehen
				addChainLinkRecursive(i, testSet, nextJoinedEC, counter);

				// backtrack: Auswahl rückgängig machen
				testSet.remove(testSet.size() - 1);
			} else {
				mLogger.info("not adding " + req.mName + " because of ChainLinkTest");
			}
		}
	}

	private void fillwithSingles(final List<ReqsWithAttributes> testSet, Term joinedEC) {

		mLogger.info("try to fill with singles");
		for (final ReqsWithAttributes req : testSet) {
			mLogger.info(
					"----------------------------------------------------------------------CHAINLINK:" + req.mName);
		}
		joinedEC = testSet.get(0).mFullExitCondition;
		for (int i = 1; i < testSet.size(); i++) {
			joinedEC = SmtUtils.and(mScript, joinedEC, testSet.get(i).mFullExitCondition);
		}
		joinedEC = SmtUtils.toDnf(mServices, mManagedScript, joinedEC);
		final Term[] exitConditions = SmtUtils.getDisjuncts(joinedEC);
		final List<List<ReqsWithAttributes>> list = new ArrayList<>();
		boolean help = true;
		final TermVariable[] Variables = joinedEC.getFreeVars();
		final List<ReqsWithAttributes> potentialReqs = new ArrayList();

		for (final TermVariable var : Variables) {
			if (!mDictVar.containsKey(var)) {
				help = false;
				break;
			}
			potentialReqs.addAll(mDictVar.get(var));

		}

		if (help) {
			final List<ReqsWithAttributes> realReqs = new ArrayList();
			for (final ReqsWithAttributes reqs : potentialReqs) {
				boolean potiential = true;
				for (final ReqsWithAttributes chainReqs : testSet) {
					if (!mChainLinkSingles.get(chainReqs).contains(reqs)) {
						potiential = false;
						break;
					}

				}
				if (!potiential) {
					break;
				} else {
					realReqs.add(reqs);
				}
			}
			mLogger.info("Anzahl an möglichen Requirements: " + realReqs.size());
			singleRecursiveAdd(testSet, realReqs, Arrays.asList(exitConditions), new ArrayList());
		}

	}

	private void singleRecursiveAdd(final List<ReqsWithAttributes> testSet, final List<ReqsWithAttributes> singles,
			final List<Term> exitConditions, final List<ReqsWithAttributes> addedSingles) {
		mLogger.info("Anzahl Singles: " + addedSingles.size());
		mLogger.info("Try to add a single");
		for (final ReqsWithAttributes req : singles) {

			mLogger.info("next single " + req.mName);
			final List<Term> newEC = new ArrayList();

			for (final Term exitCondition : exitConditions) {
				final Term conjunction = SmtUtils.and(mScript, exitCondition, req.mFullExitCondition);
				final LBool result = SmtUtils.checkSatTerm(mScript, conjunction);
				if (result == LBool.SAT) {
					newEC.add(exitCondition);
				}

			}
			mLogger.info("EC rauslöschen abgeschlossen");

			if (newEC.size() == 0) {
				mLogger.info("keine freien exit ptions mehr");
				addedSingles.add(req);

				if (!mRTICombinations.contains(addedSingles)) {
					boolean alreadyContained = false;

					for (final List<ReqsWithAttributes> rtisFound : mRTICombinations) {
						if (addedSingles.containsAll(rtisFound)) {
							mLogger.info("rausgeschmissen weil schon drin");
							alreadyContained = true;
							break;
						}
					}

					if (!alreadyContained) {
						final List<ReqsWithAttributes> ll = new ArrayList<>(addedSingles);
						ll.addAll(testSet);

						if (!makePreCheckFromList(ll)) {
							mRTICombinations.add(ll);
							mRTIReturnSet.add(rtiSetsFormatted(ll));
							mLogger.info("RTI WITH CHAINLINK FOUND");
						} else {
							mLogger.info("RTI WITH CHAINLINK NOT FOUND");
						}

					}
				}

			} else {
				mLogger.info("noch exit options übrig");

				if (newEC.size() < exitConditions.size()) {
					addedSingles.add(req);
					mLogger.info("testSetverkleinert");
					final List<ReqsWithAttributes> help = new ArrayList<>(singles.subList(1, singles.size()));
					final List<ReqsWithAttributes> newSingles = new ArrayList<>(singles.subList(1, singles.size()));

					singleRecursiveAdd(testSet, newSingles, newEC, addedSingles);
				} else {
					mLogger.info("req hat nicht gepasst");
				}

			}

		}

	}

	private boolean compatibiiltyCheck(final ReqsWithAttributes reqsWithAttributes,
			final ReqsWithAttributes reqsWithAttributes2) {
		mLogger.info("RTI check for " + reqsWithAttributes.mName + " and " + reqsWithAttributes2.mName);
		mLogger.info(reqsWithAttributes.mCounterTrace);
		mLogger.info(reqsWithAttributes2.mCounterTrace);

		boolean help = true;
		if (!habenSchnittmenge(reqsWithAttributes.mFullExitCondition.getFreeVars(),
				reqsWithAttributes.mFullExitCondition.getFreeVars())) {
			return false;
		}
		Term conjunction = null;
		LBool result = null;
		if (((reqsWithAttributes.mBeforeMaxPhase != null && reqsWithAttributes2.mBeforeMaxPhase != null)
				&& reqsWithAttributes.mPenultimatePhase.mBound.equals(reqsWithAttributes2.mPenultimatePhase.mBound))
				&& (reqsWithAttributes.mPenultimatePhase.mBound == reqsWithAttributes2.mPenultimatePhase.mBound)) {

			conjunction = SmtUtils.and(mScript, reqsWithAttributes.mBeforeMaxPhase.mInvariant,
					reqsWithAttributes2.mBeforeMaxPhase.mInvariant);
			result = SmtUtils.checkSatTerm(mScript, conjunction);
			if (result == LBool.UNSAT) {
				mLogger.info("aussportiert wegen BeforeMaxPhase invariant");
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
			mLogger.info("aussportiert wegen MaxPhase invariant");
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

	private void OldfillwithSingles(final List<ReqsWithAttributes> testSet, Term joinedEC) {
		mLogger.info("try to fill with singles");
		joinedEC = testSet.get(0).mFullExitCondition;
		for (int i = 1; i < testSet.size(); i++) {
			joinedEC = SmtUtils.and(mScript, joinedEC, testSet.get(i).mFullExitCondition);
		}
		joinedEC = SmtUtils.toDnf(mServices, mManagedScript, joinedEC);
		final Term[] exitConditions = SmtUtils.getDisjuncts(joinedEC);
		final List<List<ReqsWithAttributes>> list = new ArrayList<>();
		boolean help = true;

		for (final Term exitOption : exitConditions) {
			final List<ReqsWithAttributes> helpList = new ArrayList<>();
			final TermVariable[] Variables = exitOption.getFreeVars();

			for (final TermVariable variable : Variables) {
				mLogger.info(variable);
				if (mDictVar.containsKey(variable) && mDictVar.get(variable).size() > 0) {
					helpList.addAll(mDictVar.get(variable));
				}
			}

			if (helpList.size() != 0) {
				list.add(helpList);
			} else {
				mLogger.info("keine rti möglich");
				help = false;
			}
		}
		if (help) {
			mLogger.info("erstmal " + cartesianProduct(list).size());

			for (final List<ReqsWithAttributes> reqCombo : cartesianProduct(list)) {
				mLogger.info("neuer Vergleich");
				for (final ReqsWithAttributes req : testSet) {
					mLogger.info("chainLink enthält " + req.mName);
				}
				for (final ReqsWithAttributes req : reqCombo) {
					mLogger.info("single enthält " + req.mName);
				}

				if (!mRTICombinations.contains(reqCombo)) {
					boolean alreadyContained = false;

					for (final List<ReqsWithAttributes> rtisFound : mRTICombinations) {
						if (reqCombo.containsAll(rtisFound)) {
							mLogger.info("rausgeschmissen weil schon drin");
							alreadyContained = true;
							break;
						}
					}

					if (!alreadyContained) {
						final List<ReqsWithAttributes> ll = new ArrayList<>(reqCombo);
						ll.addAll(testSet);

						if (!makePreCheckFromList(ll)) {
							mRTICombinations.add(ll);
							mRTIReturnSet.add(rtiSetsFormatted(ll));
							mLogger.info("RTI WITH CHAINLINK FOUND");
						} else {
							mLogger.info("RTI WITH CHAINLINK NOT FOUND");
						}

					}
				}
			}
		}

	}

	private boolean makePreCheckFromList(final List<ReqsWithAttributes> reqs) {
		// check exit conditions
		Term combination = reqs.get(0).mFullExitCondition;
		for (int i = 1; i < reqs.size(); i++) {
			combination = SmtUtils.and(mScript, combination, reqs.get(i).mFullExitCondition);
		}
		LBool result = SmtUtils.checkSatTerm(mScript, combination);
		if (result == LBool.SAT) {
			return true;
		}

		combination = reqs.get(0).mMaxPhase.mInvariant;
		for (int i = 1; i < reqs.size(); i++) {
			combination = SmtUtils.and(mScript, combination, reqs.get(i).mMaxPhase.mInvariant);
		}
		result = SmtUtils.checkSatTerm(mScript, combination);
		if (result == LBool.UNSAT) {
			return true;
		}
		return false;
	}

	public static <ReqWithRTIPCattributes> List<List<ReqWithRTIPCattributes>>
			cartesianProduct(final List<List<ReqWithRTIPCattributes>> lists) {
		List<List<ReqWithRTIPCattributes>> result = new ArrayList<>();
		result.add(new ArrayList<>()); // Start with empty combination

		for (final List<ReqWithRTIPCattributes> sublist : lists) {
			final List<List<ReqWithRTIPCattributes>> temp = new ArrayList<>();
			for (final List<ReqWithRTIPCattributes> combination : result) {
				for (final ReqWithRTIPCattributes element : sublist) {
					final List<ReqWithRTIPCattributes> newCombination = new ArrayList<>(combination);
					newCombination.add(element);

					// Remove duplicates manually
					final List<ReqWithRTIPCattributes> deduped = new ArrayList<>();
					for (final ReqWithRTIPCattributes item : newCombination) {
						if (!deduped.contains(item)) {
							deduped.add(item);
						}
					}

					temp.add(deduped);
				}
			}
			result = temp;
		}
		return result;
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
				mLogger.info("aussportiert wegen BeforeMaxPhase invariant");

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
		mLogger.info("RTI check for " + reqsWithAttributes.mName + " and " + reqsWithAttributes2.mName);
		mLogger.info(reqsWithAttributes.mCounterTrace);
		mLogger.info(reqsWithAttributes2.mCounterTrace);
		boolean help = true;

		Term conjunction =
				SmtUtils.and(mScript, reqsWithAttributes.mFullExitCondition, reqsWithAttributes2.mFullExitCondition);
		LBool result = SmtUtils.checkSatTerm(mScript, conjunction);
		if (result != LBool.UNSAT) {
			mLogger.info("aussportiert wegen ExitCondition passen nicht");
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
				mLogger.info("aussportiert wegen BeforeMaxPhase invariant");
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
			mLogger.info("aussportiert wegen MaxPhase invariant");
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
				newReq.mExitConditions = SmtUtils.getDisjuncts(newReq.mFullExitCondition);
				if (newReq.mExitConditions.length > 1) {
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
