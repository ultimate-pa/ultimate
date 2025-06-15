package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.NonDeterministicChoice;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.Restriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.EqualityExtractor.EdgeUntranslatableError;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.Update.AssignmentUpdate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.Update.HavocUpdate;

public class InterpretedIcfgEdge {
	private final Term mGuard;
	private final Update[] mUpdates;
	private final IcfgEdge mEdge;
	private final Set<TermVariable> mAuxVars;
	private final Set<TermVariable> mGuardVars;
	/** Variables that were read on this edge */
	private final Set<TermVariable> mReadVars;
	/** Variables that were havoced on this edge and then read on this edge */
	private final Set<TermVariable> mHavocedAndReadVars;
	/** Variables that were assigned before they were read on this edge */
	private final Set<TermVariable> mAssignedVars;

	public InterpretedIcfgEdge(final Term guard, final Update[] updateVariants, final IcfgEdge edge,
			final Set<TermVariable> auxVars) {
		mGuard = guard;
		mGuardVars = Set.of(mGuard.getFreeVars());
		mUpdates = updateVariants;
		mEdge = edge;
		mAuxVars = auxVars;

		final List<TermVariable> havocedVars = new ArrayList<>();
		final Set<TermVariable> readVars = new HashSet<>(mGuardVars);
		final List<TermVariable> havocedAndReadVars = new ArrayList<>();
		final List<TermVariable> assignedVars = new ArrayList<>();

		for (final Update update : mUpdates) {
			readVars.addAll(update.getFreeVars());

			switch (update) {
			case final HavocUpdate hu:
				havocedVars.add(hu.getVariable());
				break;
			case final AssignmentUpdate au:
				if (!readVars.contains(au.getVariable())) {
					assignedVars.add(au.getVariable());
				}
				break;
			default:
				break;
			}

			havocedAndReadVars
					.addAll(update.getFreeVars().stream().filter(termVar -> havocedVars.contains(termVar)).toList());
		}

		mHavocedAndReadVars = Set.copyOf(havocedAndReadVars);
		readVars.removeAll(mAuxVars);
		mReadVars = Set.copyOf(readVars);
		mAssignedVars = Set.copyOf(assignedVars);
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

	public void update(final Map<Term, Value> state, final NonDeterministicChoice ndc,
			final Map<Term, Restriction<?>> havocRestrictions) {
		for (final Update update : mUpdates) {
			havocNeeded(state, ndc, havocRestrictions, update.getFreeVars());
			update.update(state, ndc, havocRestrictions);
		}

		for (final TermVariable auxVar : mAuxVars) {
			state.remove(auxVar);
		}
	}

	public boolean containsHavoc(final Map<Term, Value> state) {
		// Havoc happens if a variable undergoes an havoc update and is then read on this edge
		// OR when a variable underwent a havoc update in a previous state and is read on this edge.
		return mHavocedAndReadVars.size() > 0 || !state.keySet().containsAll(mReadVars);
	}

	private static void havocNeeded(final Map<Term, Value> state, final NonDeterministicChoice ndc,
			final Map<Term, Restriction<?>> havocRestrictions, final Set<TermVariable> required) {
		for (final TermVariable var : required) {
			if (state.containsKey(var)) {
				continue;
			}
			state.put(var, ndc.havoc(var.getSort(), havocRestrictions.remove(var)));
		}
	}

	/**
	 * Removes all variables that were not havoced on this edge for the purposes of propagating havocs to earlier
	 * states.
	 *
	 * @param currentVars
	 */
	public void removeSafe(final Set<Term> currentVars) {
		/*
		 * Assigned variables may have been havoced (and possibly read after the havoc update) on this edge after being
		 * assigned, but they do not need to be propagated back to earlier states if this is the case, so this is fine.
		 */
		currentVars.removeAll(mAssignedVars);
	}

	public boolean guard(final Map<Term, Value> state, final NonDeterministicChoice ndc,
			final Map<Term, Restriction<?>> havocRestrictions) {

		havocNeeded(state, ndc, havocRestrictions, mGuardVars);

		return ((BoolValue) TermEvaluator.evaluate(state, mGuard)).getValue();
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

	public Term getUpdateTerm(final Script script) {
		final List<Term> updateTerms = Arrays.asList(mUpdates).stream().map((update) -> update.toTerm(script)).toList();
		return SmtUtils.and(script, updateTerms);
	}

	public Update[] getUpdates() {
		return mUpdates;
	}

	public static class UntranslatableIcfgEdge extends InterpretedIcfgEdge {
		public UntranslatableIcfgEdge(final IcfgEdge edge) {
			super(edge.getTransformula().getFormula().getTheory().mTrue, new Update[0], edge, Set.of());
		}

		@Override
		public boolean guard(final Map<Term, Value> state, final NonDeterministicChoice ndc,
				final Map<Term, Restriction<?>> havocRestrictions) {
			throw new EdgeUntranslatableError();
		}

		@Override
		public void update(final Map<Term, Value> state, final NonDeterministicChoice ndc,
				final Map<Term, Restriction<?>> havocRestrictions) {
			throw new EdgeUntranslatableError();
		}
	}

	public static class InterpretedIcfgEdgeBuilder {
		private Update[] mUpdateArray;
		private Term mGuardTerm;
		private final IcfgEdge mGraphEdge;
		private final Set<TermVariable> mAuxVariables;

		public InterpretedIcfgEdgeBuilder(final IcfgEdge edge, final Set<TermVariable> auxVars) {
			mGraphEdge = edge;
			mAuxVariables = auxVars;
		}

		public InterpretedIcfgEdgeBuilder addUpdates(final Update[] updates) {
			mUpdateArray = updates;
			return this;
		}

		public InterpretedIcfgEdgeBuilder makeGuardUnchanged(final IUltimateServiceProvider services,
				final ManagedScript mngScript, final UnmodifiableTransFormula formula) {
			mGuardTerm = TransFormulaUtils.computeGuardTerm(services, mngScript, formula, true);
			return this;
		}

		public InterpretedIcfgEdgeBuilder makeGuardFromTerm(final IUltimateServiceProvider services,
				final ManagedScript mngScript, final UnmodifiableTransFormula formula, final Term term) {
			final TransFormulaBuilder tfb = new TransFormulaBuilder(formula.getInVars(), formula.getOutVars(),
					formula.getNonTheoryConsts().size() == 0, formula.getNonTheoryConsts(),
					formula.getBranchEncoders().size() == 0, formula.getBranchEncoders(),
					formula.getAuxVars().size() == 0);
			for (final TermVariable auxVar : formula.getAuxVars()) {
				tfb.addAuxVar(auxVar);
			}
			tfb.setFormula(term);
			tfb.setInfeasibility(formula.isInfeasible());

			final UnmodifiableTransFormula subFormula = tfb.finishConstruction(mngScript);
			mGuardTerm = TransFormulaUtils.computeGuardTerm(services, mngScript, subFormula, true);
			return this;
		}

		public InterpretedIcfgEdge finish() {
			return new InterpretedIcfgEdge(mGuardTerm, mUpdateArray, mGraphEdge, mAuxVariables);
		}
	}
}