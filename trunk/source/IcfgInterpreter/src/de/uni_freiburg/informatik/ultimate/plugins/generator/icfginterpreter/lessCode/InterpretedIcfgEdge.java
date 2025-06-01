package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode;

import java.util.Arrays;
import java.util.HashMap;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.Update.HavocUpdate;

public class InterpretedIcfgEdge {
	private final Term mGuard;
	private final Update[] mUpdates;
	private final IcfgEdge mEdge;
	private final Set<TermVariable> mAuxVars;
	private final boolean mHasHavoc;

	public InterpretedIcfgEdge(final Term guard, final Update[] updateVariants, final IcfgEdge edge,
			final Set<TermVariable> auxVars) {
		mGuard = guard;
		mUpdates = updateVariants;
		mEdge = edge;
		mAuxVars = auxVars;
		boolean hasHavoc = false;
		for (final Update update : mUpdates) {
			if (update instanceof HavocUpdate) {
				hasHavoc = true;
				break;
			}
		}
		mHasHavoc = hasHavoc;
	}

	public boolean hasHavoc() {
		return mHasHavoc;
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

	public HashMap<Term, Value> update(final Map<Term, Value> state, final NonDeterministicChoice ndc,
			final Map<Term, Restriction<?>> havocRestrictions) {
		final HashMap<Term, Value> out = new HashMap<>(state);

		for (final Update update : mUpdates) {
			update.update(out, ndc, havocRestrictions);
		}

		for (final TermVariable auxVar : mAuxVars) {
			out.remove(auxVar);
		}

		return out;
	}

	public boolean guard(final Map<Term, Value> state, final NonDeterministicChoice ndc,
			final Map<Term, Restriction<?>> havocRestrictions) {
		return ((BoolValue) TermEvaluator.evaluate(state, mGuard, ndc, havocRestrictions)).getValue();
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
		public HashMap<Term, Value> update(final Map<Term, Value> state, final NonDeterministicChoice ndc,
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