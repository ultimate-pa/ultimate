package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datastructures;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.EqualityExtractor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.EqualityExtractor.EdgeUntranslatableError;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.EqualityExtractor.Equations;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.NonDeterministicChoice;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ExecutionResult.Pair;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.RestrictionParser;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.TermEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datastructures.ArrayValue.EmptyArrayEntryException;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datastructures.Equation.SolvedEquation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datastructures.Restriction.EmptyRangeException;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datastructures.Update.HavocUpdate;

public class InterpretedIcfgEdge {
	private final Term mGuard;
	private final Update[] mUpdates;
	private final IcfgEdge mEdge;
	private final Set<TermVariable> mAuxVars;
	private final Set<TermVariable> mGuardVars;
	private final Map<Term, Pair<TermVariable, List<Term>>> mGuardArrayReads;
	/** Variables that were read on this edge */
	private final Set<TermVariable> mReadVars;
	/** Variables that were havoced on this edge. */
	private final Set<TermVariable> mHavocedVars;
	/** Variables that were havoced or assumed on this edge and then read on this edge */
	private final Set<TermVariable> mHavocedAndReadVars;
	private final Map<Term, RestrictionParser> mGuardRestrictions;
	private final ArrayList<Term> mAllVars;

	private InterpretedIcfgEdge(final Term guard, final Update[] updateVariants, final IcfgEdge edge,
			final Set<TermVariable> auxVars, final Map<Term, RestrictionParser> guardRestrictions) {
		mGuard = guard;
		mGuardVars = Set.of(mGuard.getFreeVars());
		final List<ApplicationTerm> guardSelects = Util.extractSelects(guard);

		mGuardArrayReads = guardSelects.stream()
				.collect(Collectors.toMap((select -> (Term) select), (select -> Util.selectToKeyPair(select))));
		mGuardRestrictions = guardRestrictions;

		mUpdates = updateVariants;
		mEdge = edge;
		mAuxVars = auxVars;

		final List<TermVariable> havocedVars = new ArrayList<>();
		final Set<TermVariable> readVars = new HashSet<>(mGuardVars);
		final List<TermVariable> havocedAndReadVars = new ArrayList<>();

		for (final Update update : mUpdates) {
			readVars.addAll(update.getFreeVars());

			switch (update) {
			case final HavocUpdate hu:
				havocedVars.add(hu.getVariable());

				break;
			default:
				break;
			}

			/*
			 * Updates are in order, so we only need to check the variables that have been havoced up to this point
			 */
			havocedAndReadVars.addAll(update.getFreeVars().stream().filter(havocedVars::contains).toList());
		}

		mHavocedAndReadVars = Set.copyOf(havocedAndReadVars);
		mHavocedVars = Set.copyOf(havocedVars);
		readVars.removeAll(mAuxVars);
		mReadVars = Set.copyOf(readVars);
		mAllVars = new ArrayList<>();
		mAllVars.addAll(mReadVars);
		mAllVars.addAll(mAuxVars);
	}

	public IcfgLocation getTarget() {
		return mEdge.getTarget();
	}

	public IcfgLocation getSource() {
		return mEdge.getSource();
	}

	public IcfgEdge getEdge() {
		return mEdge;
	}

	public Set<TermVariable> getHavocedVars() {
		return mHavocedVars;
	}

	public Map<TermVariable, Value> update(final Map<TermVariable, Value> state, final NonDeterministicChoice ndc,
			final Map<Term, Restriction<?>> havocRestrictions) {
		final Map<TermVariable, Value> havocedVars = new HashMap<>();
		for (final Update update : mUpdates) {
			// havoc variables and read array entries that aren't in the state
			havocedVars.putAll(
					havocOrdered(state, ndc, havocRestrictions, update.getFreeVars(), update.getArrayReads(), false));

			update.update(state, ndc, havocRestrictions);
		}

		for (final TermVariable auxVar : mAuxVars) {
			state.remove(auxVar);
		}

		return havocedVars;
	}

	public boolean containsHavoc(final Map<TermVariable, Value> state) {
		// Havoc happens if a variable undergoes an havoc update and is then read on this edge
		// OR when a variable underwent a havoc update in a previous state and is read on this edge.
		return !mHavocedAndReadVars.isEmpty() || !state.keySet().containsAll(mReadVars);
	}

	public Map<TermVariable, Value> havocOrdered(final Map<TermVariable, Value> state, final NonDeterministicChoice ndc,
			final Map<Term, Restriction<?>> havocRestrictions, final Set<TermVariable> required,
			final Map<Term, Pair<TermVariable, List<Term>>> arrayReads, final boolean useGuardRestrictions) {

		final HashSet<Term> remainingRequired = new HashSet<>(required);
		remainingRequired.addAll(arrayReads.keySet());
		final Set<Term> completedTerms = new HashSet<>();
		final Map<TermVariable, Value> havocedVars = new HashMap<>();

		while (!remainingRequired.isEmpty()) {
			for (final Term term : remainingRequired) {
				final TermVariable termVar;
				final ArrayValue array;
				final List<Value> keyValues;

				if (term instanceof final TermVariable tv) {
					if (state.containsKey(term) || !required.contains(term)) {
						completedTerms.add(term);
						continue;
					}
					termVar = tv;
					array = null;
					keyValues = null;
				} else {
					final Pair<TermVariable, List<Term>> data = arrayReads.get(term);
					if (data == null) {
						continue;
					}
					termVar = data.a();
					try {
						keyValues = new ArrayList<>();
						for (final Term key : data.b()) {
							keyValues.add(TermEvaluator.evaluate(state, key));
						}
					} catch (final Error e) {
						continue;
					}
					array = (ArrayValue) state.get(termVar);

					if ((array).hasKey(keyValues)) {
						completedTerms.add(term);
						continue;
					}
				}
				// The term must be havoced

				final Restriction<?> existingRestriction = havocRestrictions.get(term);
				final RestrictionParser guardRestriction = mGuardRestrictions.get(term);
				Restriction<?> restriction;
				if (!useGuardRestrictions || guardRestriction == null) {
					restriction = existingRestriction;
				} else if (!state.keySet().containsAll(guardRestriction.getFreeVars())) {
					// can't build guard restriction since it requires another variable that was not yet havoced
					restriction = existingRestriction;
				} else {
					try {
						if (existingRestriction != null) {
							restriction = existingRestriction.combine(guardRestriction.getRestriction(state));
						} else {
							restriction = guardRestriction.getRestriction(state);
						}
					} catch (final EmptyRangeException a) {
						// The new range contains no values.
						// We simply use the existing restriction to havoc a value.
						// The guard will be false!
						restriction = existingRestriction;
					} catch (final EmptyArrayEntryException b) {
						// The guard restriction calls on an array entry that is still undetermined.
						// We will resolve non-array variables first.
						restriction = existingRestriction;
					}
				}

				if (array == null) {
					final Value havocResult = ndc.havoc(termVar.getSort(), restriction);
					state.put(termVar, havocResult);
					havocedVars.put(termVar, havocResult);
					completedTerms.add(term);
				} else {
					state.put(termVar, array.store(keyValues, ndc.havoc(array.getValueSort(), restriction)));
					// Arrays are not havoced as a whole, neither are their entries.
					completedTerms.add(termVar);
				}
				havocRestrictions.remove(term);
			}
			remainingRequired.removeAll(completedTerms);
			completedTerms.clear();
		}

		return havocedVars;
	}

	/**
	 * Removes all variables that were havoced on this edge for the purposes of propagating the value to the state where
	 * the variable was initially havoced.
	 *
	 * @param currentVars
	 */
	public void removeSafe(final Set<TermVariable> currentVars) {
		/*
		 * If a variable was havoced and then read on this edge, then it should not be propagated to earlier states.
		 */
		currentVars.removeAll(mHavocedAndReadVars);
	}

	public Pair<Boolean, Map<TermVariable, Value>> guard(final Map<TermVariable, Value> state,
			final NonDeterministicChoice ndc, final Map<Term, Restriction<?>> havocRestrictions) {
		final Map<TermVariable, Value> havocedVars =
				havocOrdered(state, ndc, havocRestrictions, mGuardVars, mGuardArrayReads, true);

		return new Pair<>(((BoolValue) TermEvaluator.evaluate(state, mGuard)).getValue(), havocedVars);
	}

	@Override
	public String toString() {
		final StringBuilder out = new StringBuilder();

		out.append("From ").append(getSource().toString()).append(" to ").append(getTarget().toString());
		out.append("\nGuard: ").append(mGuard.toStringDirect());
		if (mUpdates.length == 0) {
			out.append("\nNo updates.");
		} else {
			out.append("\nUpdates:");
		}

		for (final Update update : mUpdates) {
			out.append("\n\t").append(update.toString());
		}

		out.append("\n Original edge: ").append(mEdge.toString());
		return out.toString();
	}

	public Term getGuardTerm() {
		return mGuard;
	}

	public Update[] getUpdates() {
		return mUpdates;
	}

	public static class UntranslatableIcfgEdge extends InterpretedIcfgEdge {
		public UntranslatableIcfgEdge(final IcfgEdge edge) {
			super(edge.getTransformula().getFormula().getTheory().mTrue, new Update[0], edge, Set.of(), Map.of());
		}

		@Override
		public Pair<Boolean, Map<TermVariable, Value>> guard(final Map<TermVariable, Value> state,
				final NonDeterministicChoice ndc, final Map<Term, Restriction<?>> havocRestrictions) {
			throw new EdgeUntranslatableError();
		}

		@Override
		public Map<TermVariable, Value> update(final Map<TermVariable, Value> state, final NonDeterministicChoice ndc,
				final Map<Term, Restriction<?>> havocRestrictions) {
			throw new EdgeUntranslatableError();
		}
	}

	public static class InterpretedIcfgEdgeBuilder {
		private Update[] mUpdateArray;
		private Term mGuardTerm;
		private final IcfgEdge mGraphEdge;
		private final Set<TermVariable> mAuxVariables;
		private Map<Term, RestrictionParser> mGuardRestrictions;
		private final ILogger mLogger;

		public InterpretedIcfgEdgeBuilder(final IcfgEdge edge, final Set<TermVariable> auxVars, final ILogger logger) {
			mGraphEdge = edge;
			mAuxVariables = auxVars;
			mLogger = logger;
		}

		public InterpretedIcfgEdgeBuilder addUpdates(final Update[] updates) {
			mUpdateArray = updates;
			return this;
		}

		public InterpretedIcfgEdgeBuilder makeGuardUnchanged(final IUltimateServiceProvider services,
				final ManagedScript mngScript, final UnmodifiableTransFormula formula) {
			mGuardTerm = TransFormulaUtils.computeGuardTerm(services, mngScript, formula, true);

			calculateGuardRestrictions(mngScript.getScript(), formula);
			return this;
		}

		public InterpretedIcfgEdgeBuilder makeGuardFromTerm(final IUltimateServiceProvider services,
				final ManagedScript mngScript, final UnmodifiableTransFormula formula, final Term term) {
			final TransFormulaBuilder tfb = new TransFormulaBuilder(formula.getInVars(), formula.getOutVars(),
					formula.getNonTheoryConsts().isEmpty(), formula.getNonTheoryConsts(),
					formula.getBranchEncoders().isEmpty(), formula.getBranchEncoders(), formula.getAuxVars().isEmpty());
			for (final TermVariable auxVar : formula.getAuxVars()) {
				tfb.addAuxVar(auxVar);
			}
			tfb.setFormula(term);
			tfb.setInfeasibility(formula.isInfeasible());

			final UnmodifiableTransFormula subFormula = tfb.finishConstruction(mngScript);
			mGuardTerm = TransFormulaUtils.computeGuardTerm(services, mngScript, subFormula, true);

			calculateGuardRestrictions(mngScript.getScript(), subFormula);
			return this;
		}

		private void calculateGuardRestrictions(final Script script, final UnmodifiableTransFormula formula) {
			final Equations equations = EqualityExtractor.extract(mGuardTerm, script, formula, mLogger);
			final List<SolvedEquation> solvedEquations = new ArrayList<>(equations.solveForAllVars(script));

			final Map<Term, RestrictionParser> guardRestrictions = new HashMap<>();

			final ArrayDeque<Term> havocOrder = new ArrayDeque<>();

			while (!solvedEquations.isEmpty()) {
				final Term solvedFor = solvedEquations.get(0).getLhs();

				// Havoc InVars before AuxVars
				if (formula.getInVars().containsValue(solvedFor)) {
					havocOrder.addFirst(solvedFor);
				} else {
					havocOrder.addLast(solvedFor);
				}

				final List<SolvedEquation> varEquations =
						solvedEquations.stream().filter(eq -> eq.getLhs().equals(solvedFor)).toList();
				solvedEquations.removeAll(varEquations);

				RestrictionParser parser;
				if (solvedFor instanceof ApplicationTerm at) {
					TermVariable arrayVar = null;
					while (arrayVar == null) {
						final Term array = at.getParameters()[0];
						if (array instanceof final TermVariable tv) {
							arrayVar = tv;
						}
						if (array instanceof final ApplicationTerm subAt) {
							assert subAt.getFunction().getName().equals(SMTLIBConstants.SELECT);
							at = subAt;
						}
					}

					parser = new RestrictionParser(arrayVar, at, varEquations);
				} else {
					parser = new RestrictionParser((TermVariable) solvedFor, varEquations);
				}

				guardRestrictions.put(solvedFor, parser);
			}

			mGuardRestrictions = Map.copyOf(guardRestrictions);
		}

		public InterpretedIcfgEdge finish() {
			return new InterpretedIcfgEdge(mGuardTerm, mUpdateArray, mGraphEdge, mAuxVariables, mGuardRestrictions);
		}
	}
}