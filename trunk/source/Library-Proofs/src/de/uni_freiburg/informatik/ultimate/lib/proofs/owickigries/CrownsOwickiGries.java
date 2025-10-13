/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE Proofs Library.
 *
 * The ULTIMATE Proofs Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Proofs Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Proofs Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Proofs Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Proofs Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.MonolithicImplicationChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.crown.Crown;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.crown.CrownConstruction;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.crown.CrownsEmpire;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.EmpireAnnotation;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.EmpireToOwickiGries;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.EmpireValidityCheck;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.PetriOwickiGries;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

public class CrownsOwickiGries<L extends IAction, P> implements IPetriNetProofProducer<L, P> {
	public static final boolean IGNORE_CUTOFF_CONDITIONS = true;

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final IPetriNet<L, P> mProgram;
	private final ManagedScript mMgdScript;
	private final IIcfgSymbolTable mSymbolTable;
	private final Set<String> mProcedures;
	private final ModifiableGlobalsTable mModifiableGlobals;
	private final BasicPredicateFactory mFactory;
	private final Function<P, IPredicate> mAssertionPlace2Assertion;

	private final Statistics mStatistics;

	private BranchingProcess<L, P> mRefinedUnfolding;
	private Set<Condition<L, P>> mOriginalConditions;
	private Set<Condition<L, P>> mAssertionConditions;
	private Function<Transition<L, P>, Transition<L, P>> mDiff2OriginalTransition = Function.identity();

	private OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> mOwickiGries;

	public CrownsOwickiGries(final IUltimateServiceProvider services, final IPetriNet<L, P> program,
			final CfgSmtToolkit csToolkit, final BasicPredicateFactory predicateFactory,
			final Function<P, IPredicate> assertionPlace2Assertion) {
		this(services, program, csToolkit.getManagedScript(), csToolkit.getSymbolTable(), csToolkit.getProcedures(),
				csToolkit.getModifiableGlobalsTable(), predicateFactory, assertionPlace2Assertion);
	}

	public CrownsOwickiGries(final IUltimateServiceProvider services, final IPetriNet<L, P> program,
			final ManagedScript mgdScript, final IIcfgSymbolTable symbolTable, final Set<String> procedures,
			final ModifiableGlobalsTable modifiableGlobals, final BasicPredicateFactory predicateFactory,
			final Function<P, IPredicate> assertionPlace2Assertion) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(getClass());
		mProgram = program;
		mMgdScript = mgdScript;
		mSymbolTable = symbolTable;
		mProcedures = procedures;
		mModifiableGlobals = modifiableGlobals;
		mFactory = predicateFactory;
		mAssertionPlace2Assertion = assertionPlace2Assertion;

		mStatistics = new Statistics(mLogger);
	}

	@Override
	public void refine(final IPredicateUnifier unifier, final INestedWordAutomaton<L, IPredicate> interpolantAutomaton,
			final Map<Transition<L, P>, Transition<L, P>> transitionBacktranslation) {
		mDiff2OriginalTransition = mDiff2OriginalTransition.compose(transitionBacktranslation::get);
	}

	@Override
	public void finalize(final IPetriNetSuccessorProvider<L, P> refinedNet,
			final BranchingProcess<L, P> refinedNetUnfolding) {
		mRefinedUnfolding = refinedNetUnfolding;
		final var conditions = getConditions(refinedNetUnfolding);
		mOriginalConditions = getOriginalConditions(conditions);
		mAssertionConditions = DataStructureUtils.difference(conditions, mOriginalConditions);
	}

	@Override
	public IPetriNet<L, P> getProgram() {
		return mProgram;
	}

	@Override
	public boolean isReadyToComputeProof() {
		return mRefinedUnfolding != null;
	}

	@Override
	public OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> getOrComputeProof() {
		if (mOwickiGries == null) {
			final var crown = getCrown();
			mLogger.debug("Constructed Crown:\n%s", crown);

			final var empire = getEmpireAnnotationFromCrown(crown);
			mLogger.debug("Constructed Empire Annotation:\n%s", empire);

			assert checkEmpireValidity(empire) : "Empire annotation is invalid";

			mOwickiGries = getOwickiGriesAnnotation(empire);
			mLogger.debug("Computed Owicki-Gries annotation:\n%s", mOwickiGries);

			assert checkOwickiGriesValidity(mOwickiGries) : "Owicki Gries annotation is invalid";
		}
		return mOwickiGries;
	}

	private Crown<P, L> getCrown() {
		final var crownConstruction =
				new CrownConstruction<>(mServices, mRefinedUnfolding, mOriginalConditions, mAssertionConditions);
		mStatistics.reportCrownStatistics(crownConstruction);
		return crownConstruction.getCrown();
	}

	private EmpireAnnotation<P> getEmpireAnnotationFromCrown(final Crown<P, L> crown) {
		mStatistics.startEmpireComputation();
		try {
			final CrownsEmpire<P, L> crownsEmpire = crown.getCrownsEmpire(mFactory, mAssertionPlace2Assertion);
			mStatistics.reportEmpire(crownsEmpire);
			return crownsEmpire.getEmpireAnnotation();
		} finally {
			mStatistics.stopEmpireComputation();
		}
	}

	private boolean checkEmpireValidity(final EmpireAnnotation<P> empire) {
		mStatistics.startEmpireValidity();
		try {
			final var implicationChecker = new MonolithicImplicationChecker(mServices, mMgdScript);
			final var checker = new EmpireValidityCheck<>(mServices, mMgdScript, implicationChecker, mFactory, mProgram,
					mModifiableGlobals, empire);
			return checker.getValidity() != Validity.INVALID;
		} finally {
			mStatistics.stopEmpireValidity();
		}
	}

	private OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>>
			getOwickiGriesAnnotation(final EmpireAnnotation<P> empire) {
		mStatistics.startOwickiGriesComputation();
		try {
			final var possibleInterferences = PetriOwickiGries.getPossibleInterferences(mRefinedUnfolding,
					mProgram.getPlaces(), mDiff2OriginalTransition);
			final EmpireToOwickiGries<L, P> empireToOwickiGries = new EmpireToOwickiGries<>(mServices, mMgdScript,
					mProgram, mSymbolTable, mProcedures, empire, possibleInterferences);
			final var annotation = empireToOwickiGries.getAnnotation();
			mStatistics.reportOwickiGries(annotation);
			return annotation;
		} finally {
			mStatistics.stopOwickiGriesComputation();
		}
	}

	private boolean checkOwickiGriesValidity(final OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> annotation) {
		mStatistics.startOwickiGriesValidity();
		try {
			final var validity =
					new PetriOwickiGriesValidityCheck<>(mServices, mMgdScript, mProgram, mModifiableGlobals, annotation)
							.isValid();
			assert validity != Validity.INVALID : "Owicki-Gries annotation is invalid";
			if (validity == Validity.UNKNOWN) {
				mLogger.warn("Could not prove validity of Owicki-Gries annotation");
			}
			return validity != Validity.INVALID;
		} finally {
			mStatistics.stopOwickiGriesValidity();
		}
	}

	private Set<Condition<L, P>> getConditions(final BranchingProcess<L, P> unfolding) {
		Set<Condition<L, P>> conditions;
		if (IGNORE_CUTOFF_CONDITIONS) {
			mLogger.info("Ignoring conditions belonging to cutoff events.");
			conditions = unfolding.getConditions().stream().filter(c -> !isCutoff(c)).collect(Collectors.toSet());
		} else {
			conditions = unfolding.getConditions().stream().collect(Collectors.toSet());
		}
		return conditions;
	}

	private static final boolean isCutoff(final Condition<?, ?> cond) {
		return cond.getPredecessorEvent().isCutoffEvent();
	}

	private Set<Condition<L, P>> getOriginalConditions(final Set<Condition<L, P>> conditions) {
		final Set<Condition<L, P>> result = new HashSet<>();
		for (final Condition<L, P> cond : conditions) {
			if (mProgram.getPlaces().contains(cond.getPlace())) {
				result.add(cond);
			}
		}
		return result;
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
	}

	private static final class Statistics extends OwickiGriesStatistics {
		public static final String CROWN_STATISTICS = "Crown construction";

		private IStatisticsDataProvider mCrownStatistics;

		public Statistics(final ILogger logger) {
			super(logger, CrownsEmpire.class, EmpireToOwickiGries.class);

			forward(CROWN_STATISTICS, () -> mCrownStatistics);
		}

		public void reportCrownStatistics(final CrownConstruction<?, ?> crownConstruction) {
			mCrownStatistics = crownConstruction.getStatistics();
		}

		public void reportEmpire(final CrownsEmpire<?, ?> computation) {
			reportEmpireStatistics(computation.getStatistics(), computation.getEmpireAnnotation());
		}
	}
}
