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
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace.DCPhase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType.ReqPeas;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.CddToSmt;

public class RTInconsistencyPreCheck {
	private Script mScript;
	private ILogger mLogger;
	private CddToSmt mCddToSmt;
	public List<ReqWithRTIPCattributes> mListWithChainLinkReqs;
	public Map<TermVariable, List<ReqWithRTIPCattributes>> VariablesDict;
	public List<Entry<PatternType<?>, PhaseEventAutomata>[]> mrtiSets;
	public List<List<ReqWithRTIPCattributes>> mRtiSetsAll;
	public int mCombinationNum;

	public class ReqWithRTIPCattributes {
		public String mName; // not important, just for debug reasons
		public ReqPeas mOriginalPea;
		public DCPhase mPenultimatePhase;
		public DCPhase mMaxPhase;
		public PhaseEventAutomata mPEA;

		public List<Term> mExitOptions;
		public Term mFullExitOption;
		public Term mTermInvariantMaxPhase;
		public boolean mChainLinkReq;
		public Term mPhaseBeforeMaxPhase;

		public ReqWithRTIPCattributes(final ReqPeas reqPea) {
			mOriginalPea = reqPea;
		}
	}

	/**
	 * This method is used to check the RTI sets of the requirements. First single reqs (so depth of search = 2), later
	 * sets with chain-link requirements (depth of search >= 3)
	 *
	 * @param reqs
	 *            List of ReqWithRTIPCattributes containing the requirements to be formatted.
	 * @return An array of Map.Entry objects representing the formatted RTI sets.
	 */
	public List<Entry<PatternType<?>, PhaseEventAutomata>[]> doRtiPreCheck(final List<ReqPeas> reqPeas,
			final ILogger logger, final Script script, final CddToSmt cddToSmt, final int range) {
		mScript = script;
		mLogger = logger;
		mCddToSmt = cddToSmt;
		mCombinationNum = range;
		mListWithChainLinkReqs = new ArrayList<>();
		VariablesDict = new HashMap();
		mrtiSets = new ArrayList<>();
		mRtiSetsAll = new ArrayList<>();

		getAttributesForReqs(reqPeas);

		for (final Map.Entry<TermVariable, List<ReqWithRTIPCattributes>> varialesList : VariablesDict.entrySet()) {
			for (int i = 0; i < varialesList.getValue().size(); i++) {
				final ReqWithRTIPCattributes req1 = varialesList.getValue().get(i);

				for (int j = i + 1; j < varialesList.getValue().size(); j++) {
					final ReqWithRTIPCattributes req2 = varialesList.getValue().get(j);
					mLogger.info("---------Neuer Vergleich---------");
					mLogger.info(req1.mName);
					mLogger.info(req2.mName);

					final Entry<PatternType<?>, PhaseEventAutomata>[] combo =
							rtiSetsFormatted(Arrays.asList(req1, req2));
					if (!mrtiSets.contains(combo) && !makePreCheck(req1, req2)) {
						mrtiSets.add(combo);

					}
				}
			}
		}
		doChainLinkTest();

		// for chain-link requirements
		if (mCombinationNum >= 1) {
			int counter = 1;
			while (counter <= mCombinationNum) {
				counter++;
				mLogger.info("START DOING CHAIN REQS");
				mLogger.info("depth:" + counter);

				for (final ReqWithRTIPCattributes req : mListWithChainLinkReqs) {
					boolean help = true;
					mLogger.info("---------Neuer Vergleich---------");
					mLogger.info(req.mName);
					mLogger.info(req.mOriginalPea.getPattern().toString());

					final List<List<ReqWithRTIPCattributes>> list = new ArrayList<>();
					for (final Term exitOption : req.mExitOptions) {
						final List<ReqWithRTIPCattributes> helpList = new ArrayList<>();
						final List<ReqWithRTIPCattributes> actualList = new ArrayList<>();
						final TermVariable[] Variables = exitOption.getFreeVars();
						for (final TermVariable variable : Variables) {
							mLogger.info(variable);
							if (VariablesDict.containsKey(variable) && VariablesDict.get(variable).size() > 0) {
								helpList.addAll(VariablesDict.get(variable));
							}
						}
						for (final ReqWithRTIPCattributes huhu : helpList) {
							if (!makePreCheckForChainLink(huhu, req, exitOption)) {
								actualList.add(huhu);
							}
						}

						if (actualList.size() != 0) {
							list.add(actualList);
						} else {
							mLogger.info("keine rti möglich");
							help = false;
							break;

						}

					}
					if (help) {
						mLogger.info("erstmal" + cartesianProduct(list).size());
						for (final List<ReqWithRTIPCattributes> reqCombo : cartesianProduct(list)) {
							mLogger.info("neuer Vegleich");
							if (!mrtiSets.contains(reqCombo)) {
								for (final List<ReqWithRTIPCattributes> rtisFound : mRtiSetsAll) {
									if (reqCombo.containsAll(rtisFound)) {
										mLogger.info("rausgeschmissen weil schon drin");
										continue;
									}

								}

								final List<ReqWithRTIPCattributes> ll = new ArrayList<>(reqCombo);
								ll.add(req);
								if (!makePreCheckFromList(ll) && !mrtiSets.contains(rtiSetsFormatted(ll))) {
									mrtiSets.add(rtiSetsFormatted(ll));
									mLogger.info("RTI WITH CHIANLINKL FOUND");
								}

							}
						}
					}

				}
			}
		}

		// ✅ Logger-Ausgaben und Rückgabe jetzt innerhalb der Methode
		mLogger.info("PreCheck found possible rt-inconsistent sets::");
		mLogger.info("Number of sets: " + mrtiSets.size());
		for (final Entry<PatternType<?>, PhaseEventAutomata>[] rtiSet : mrtiSets) {
			mLogger.info("----------RTI SET-----------:");
			for (final Entry<PatternType<?>, PhaseEventAutomata> entry : rtiSet) {
				mLogger.info(entry.getValue().getName() + ":" + entry.getKey().toString());
			}
		}

		return mrtiSets;
	}

	private void doChainLinkTest()
	{
		int counter = 1;
		while (counter <= mCombinationNum) {
			for(final ReqWithRTIPCattributes req: ) {
				counter ++;
			}
		}
		// TODO Auto-generated method stub

	}

	/**
	 * Formats the RTI sets into an array of entries with PatternType and PhaseEventAutomata. This Format is needed for
	 * the actual RTI check in the BoogieGenerator.
	 *
	 * @param reqs
	 *            List of ReqWithRTIPCattributes containing the requirements to be formatted.
	 * @return An array of Map.Entry objects representing the formatted RTI sets.
	 */
	public Entry<PatternType<?>, PhaseEventAutomata>[] rtiSetsFormatted(final List<ReqWithRTIPCattributes> reqs) {
		final List<Map.Entry<PatternType<?>, PhaseEventAutomata>> entryList = new ArrayList<>();
		for (final ReqWithRTIPCattributes req : reqs) {
			final Map.Entry<PatternType<?>, PhaseEventAutomata> entry1 =
					new AbstractMap.SimpleEntry<>(req.mOriginalPea.getPattern(), req.mPEA);
			entryList.add(entry1);
		}
		final Map.Entry<PatternType<?>, PhaseEventAutomata>[] entryArray = entryList.toArray(new Map.Entry[0]);
		Arrays.sort(entryArray, Comparator.comparing(Map.Entry::getValue));
		return entryArray;
	}

	/**
	 * Computes the Cartesian product of a list of lists of Requirements.
	 *
	 * @param lists
	 *            A list of lists, where each sublist contains elements to be combined.
	 * @return A list containing all combinations of elements from the input lists.
	 */
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

	/*
	 * This method is used to check if the two requirements are rt-inconsistent. RETURN true if they are rt-consistent
	 * RETURN false if they are rt-inconsistent
	 */
	private boolean makePreCheck(final ReqWithRTIPCattributes req1, final ReqWithRTIPCattributes req2) {
		// check exit conditions
		Term combination = SmtUtils.and(mScript, req1.mFullExitOption, req2.mFullExitOption);
		LBool result = SmtUtils.checkSatTerm(mScript, combination);
		if (result != LBool.UNSAT) {
			return true;
		}
		mRtiSetsAll.add(Arrays.asList(req1, req2));
		// Check if the Max Phases can be combined
		combination = SmtUtils.and(mScript, req1.mTermInvariantMaxPhase, req2.mTermInvariantMaxPhase);
		result = SmtUtils.checkSatTerm(mScript, combination);
		if (result == LBool.UNSAT) {
			return true;
		}

		if (req1.mMaxPhase.getBoundType() != 0 && req2.mMaxPhase.getBoundType() != 0
				&& req1.mTermInvariantMaxPhase == req2.mTermInvariantMaxPhase) {
			if (((req1.mMaxPhase.getBoundType() > 0) && req2.mMaxPhase.getBoundType() < 0)
					&& (req1.mMaxPhase.getBound() > req2.mMaxPhase.getBound())) {
				return true;
			}
		}

		if (req2.mMaxPhase.getBoundType() != 0 && req1.mMaxPhase.getBoundType() != 0
				&& req1.mTermInvariantMaxPhase == req2.mTermInvariantMaxPhase) {
			if (((req2.mMaxPhase.getBoundType() > 0) && req2.mMaxPhase.getBoundType() < 0)
					&& (req2.mMaxPhase.getBound() > req1.mMaxPhase.getBound())) {
				return true;
			}
		}

		if ((req1.mPenultimatePhase.getBoundType() == req2.mPenultimatePhase.getBoundType())
				&& (req1.mPenultimatePhase.getBound() == req2.mPenultimatePhase.getBound())) {
			combination = SmtUtils.and(mScript, req1.mPhaseBeforeMaxPhase, req2.mPhaseBeforeMaxPhase);
			result = SmtUtils.checkSatTerm(mScript, combination);
			if (result == LBool.UNSAT) {
				return true;
			}
		}
		return false;
	}

	private boolean makePreCheckForChainLink(final ReqWithRTIPCattributes req1, final ReqWithRTIPCattributes req2,
			final Term exitOption) {
		// check exit conditions
		Term combination = SmtUtils.and(mScript, req1.mFullExitOption, exitOption);
		LBool result = SmtUtils.checkSatTerm(mScript, combination);
		if (result != LBool.UNSAT) {
			return true;
		}
		mRtiSetsAll.add(Arrays.asList(req1, req2));
		// Check if the Max Phases can be combined
		combination = SmtUtils.and(mScript, req1.mTermInvariantMaxPhase, req2.mTermInvariantMaxPhase);
		result = SmtUtils.checkSatTerm(mScript, combination);
		if (result == LBool.UNSAT) {
			return true;
		}

		if (req1.mMaxPhase.getBoundType() != 0 && req2.mMaxPhase.getBoundType() != 0
				&& req1.mTermInvariantMaxPhase == req2.mTermInvariantMaxPhase) {
			if (((req1.mMaxPhase.getBoundType() > 0) && req2.mMaxPhase.getBoundType() < 0)
					&& (req1.mMaxPhase.getBound() > req2.mMaxPhase.getBound())) {
				return true;
			}
		}

		if (req2.mMaxPhase.getBoundType() != 0 && req1.mMaxPhase.getBoundType() != 0
				&& req1.mTermInvariantMaxPhase == req2.mTermInvariantMaxPhase) {
			if (((req2.mMaxPhase.getBoundType() > 0) && req2.mMaxPhase.getBoundType() < 0)
					&& (req2.mMaxPhase.getBound() > req1.mMaxPhase.getBound())) {
				return true;
			}
		}

		if ((req1.mPenultimatePhase.getBoundType() == req2.mPenultimatePhase.getBoundType())
				&& (req1.mPenultimatePhase.getBound() == req2.mPenultimatePhase.getBound())) {
			combination = SmtUtils.and(mScript, req1.mPhaseBeforeMaxPhase, req2.mPhaseBeforeMaxPhase);
			result = SmtUtils.checkSatTerm(mScript, combination);
			if (result == LBool.UNSAT) {
				return true;
			}
		}
		return false;
	}

	private boolean makePreCheckFromList(final List<ReqWithRTIPCattributes> reqs) {
		// check exit conditions
		Term combination = reqs.get(0).mFullExitOption;
		for (int i = 1; i < reqs.size(); i++) {
			combination = SmtUtils.and(mScript, combination, reqs.get(i).mFullExitOption);
		}
		LBool result = SmtUtils.checkSatTerm(mScript, combination);
		if (result == LBool.SAT) {
			return true;
		}

		combination = reqs.get(0).mTermInvariantMaxPhase;
		for (int i = 1; i < reqs.size(); i++) {
			combination = SmtUtils.and(mScript, combination, reqs.get(i).mTermInvariantMaxPhase);
		}
		result = SmtUtils.checkSatTerm(mScript, combination);
		if (result == LBool.UNSAT) {
			return true;
		}
		return false;
	}

	/*
	 * This method is used to get all the attributes of the requirements needed of the precheck. Containing
	 * PenultimatePhase, MaxPhase, FullExitOption, TermInvariantMaxPhase
	 */
	private void getAttributesForReqs(final List<ReqPeas> reqPeas) {
		for (final ReqPeas reqPea : reqPeas) {
			for (final Entry<CounterTrace, PhaseEventAutomata> reqChild : reqPea.getCounterTrace2Pea()) {
				final ReqWithRTIPCattributes newReq = new ReqWithRTIPCattributes(reqPea);
				mLogger.info(reqChild.getValue().getName()); // DEBUG
				newReq.mName = reqChild.getValue().getName(); // just for DEBUG reason

				// penultimate Phase
				newReq.mPenultimatePhase = reqChild.getKey().getPhases()[reqChild.getKey().getPhases().length - 2];
				final CDD[] exitOptionsCDD = newReq.mPenultimatePhase.getInvariant().negate().toDNF();
				newReq.mFullExitOption = mCddToSmt.toSmt(newReq.mPenultimatePhase.getInvariant().negate());
				newReq.mPEA = reqChild.getValue();

				// generate exit Options
				newReq.mExitOptions = new ArrayList<>();
				for (final CDD exitOption : exitOptionsCDD) {
					newReq.mExitOptions.add(mCddToSmt.toSmt(exitOption));
				}

				// ChainLink Reqs
				if (newReq.mExitOptions.size() > 1) {
					newReq.mChainLinkReq = true;
					mListWithChainLinkReqs.add(newReq);
				} else {
					for (final TermVariable variable : newReq.mExitOptions.get(0).getFreeVars()) {
						if (!VariablesDict.containsKey(variable)) {
							VariablesDict.put(variable, new ArrayList<>());
						}
						VariablesDict.get(variable).add(newReq);
					}
				}

				// Max Phase, needed later to eliminate false positives
				if (newReq.mPenultimatePhase.getBoundType() != 0) {
					newReq.mMaxPhase = newReq.mPenultimatePhase;
					if (reqChild.getKey().getPhases().length >= 3) {
						newReq.mPhaseBeforeMaxPhase = mCddToSmt.toSmt(
								reqChild.getKey().getPhases()[reqChild.getKey().getPhases().length - 3].getInvariant());
					}
				} else {
					newReq.mMaxPhase = reqChild.getKey().getPhases()[reqChild.getKey().getPhases().length - 3];
					if (reqChild.getKey().getPhases().length >= 4) {
						newReq.mPhaseBeforeMaxPhase = mCddToSmt.toSmt(
								reqChild.getKey().getPhases()[reqChild.getKey().getPhases().length - 4].getInvariant());
					}
				}
				newReq.mTermInvariantMaxPhase = mCddToSmt.toSmt(newReq.mMaxPhase.getInvariant());
			}
		}
	}
}
