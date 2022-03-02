package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.concurrency;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.ILattice;

public class SpecificVariableAbstraction<L extends IAction> extends VariableAbstraction<L>
		implements IRefinableAbstraction<NestedWordAutomaton<L, IPredicate>, Set<IProgramVar>, L> {

	private final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> automaton;
	private final ICopyActionFactory<L> mCopyFactory;
	private final ManagedScript mMscript;
	private final Set<IProgramVar> mAllProgramVars;
	private final Set<L> mAllLetters;
	private final ILattice<VarAbsConstraints<L>> mHierarchy;

	public SpecificVariableAbstraction(final ICopyActionFactory<L> copyFactory, final ManagedScript mscript,
			final Set<IProgramVar> allProgramVars, final Set<L> allLetters) {
		super(copyFactory, mscript, allProgramVars);
		this.automaton = null;
		mCopyFactory = copyFactory;
		mMscript = mscript;
		mAllProgramVars = allProgramVars;
		mAllLetters = allLetters;
		mHierarchy = new VarAbLattice<>(allProgramVars, mAllLetters);
	}

	public L abstractLetter(final L inLetter, final VarAbsConstraints<L> constraints) {
		if (inLetter.getTransformula().isInfeasible() == Infeasibility.INFEASIBLE
				|| nothingWillChange(inLetter, constraints)) {
			return inLetter;
		}
		final Set<IProgramVar> transformInVars = new HashSet<>(inLetter.getTransformula().getInVars().keySet());
		final Set<IProgramVar> transformIOutVars = new HashSet<>(inLetter.getTransformula().getOutVars().keySet());
		transformInVars.removeAll(constraints.getInConstraints(inLetter));
		transformIOutVars.removeAll(constraints.getOutConstraints(inLetter));
		return inLetter;
	}

	private boolean nothingWillChange(final L inLetter, final VarAbsConstraints<L> constraints) {
		// Is this sound? If every Variable, that can be assigned is in InVars .. and so on?
		if (constraints.getInConstraints(inLetter).containsAll(inLetter.getTransformula().getInVars().keySet())
				&& constraints.getOutConstraints(inLetter)
						.containsAll(inLetter.getTransformula().getInVars().keySet())) {
			return true;
		}
		return false;
	}

	public UnmodifiableTransFormula abstractTransFormula(final UnmodifiableTransFormula utf,
			final Set<IProgramVar> inTransform, final Set<IProgramVar> outTransform) {

		final Map<IProgramVar, TermVariable> nInVars = new HashMap<>(utf.getInVars());
		final Map<IProgramVar, TermVariable> nOutVars = new HashMap<>(utf.getOutVars());
		final Set<IProgramVar> assignedVars = utf.getAssignedVars();
		final Set<TermVariable> nAuxVars = new HashSet<>(utf.getAuxVars());

		for (final IProgramVar v : inTransform) {
			if (assignedVars.contains(v)) {
				nAuxVars.add(nOutVars.get(v));
				final TermVariable nov = mMscript.constructFreshCopy(nOutVars.get(v));
				nOutVars.put(v, nov);
			}
		}
		/*
		 * 
		 * for (final IProgramVar v : transform) { if (assignedVars.contains(v)) { nAuxVars.add(nOutVars.get(v)); final
		 * TermVariable nov = mMscript.constructFreshCopy(nOutVars.get(v)); nOutVars.put(v, nov); } if
		 * (nInVars.containsKey(v)) { nAuxVars.add(nInVars.get(v)); nInVars.remove(v); if (!assignedVars.contains(v)) {
		 * nOutVars.remove(v); } }
		 * 
		 * }
		 */

		final TransFormulaBuilder tfBuilder;
		final Set<IProgramConst> ntc = new HashSet<>(utf.getNonTheoryConsts());
		if (utf.getBranchEncoders().isEmpty()) {
			tfBuilder = new TransFormulaBuilder(nInVars, nOutVars, false, ntc, true, null, false);
		} else {
			final Set<TermVariable> be = new HashSet<>(utf.getBranchEncoders());
			tfBuilder = new TransFormulaBuilder(nInVars, nOutVars, false, ntc, false, be, false);
		}

		if (nAuxVars.isEmpty()) {
			tfBuilder.setFormula(utf.getFormula());
		} else {
			tfBuilder.setFormula(mMscript.getScript().quantifier(QuantifiedFormula.EXISTS,
					nAuxVars.toArray(TermVariable[]::new), utf.getFormula()));
		}
		tfBuilder.setInfeasibility(Infeasibility.NOT_DETERMINED);
		final UnmodifiableTransFormula abstracted = tfBuilder.finishConstruction(mMscript);

		assert abstracted.getAssignedVars().equals(assignedVars) : "Abstraction should not change assigned variables";
		assert utf.getInVars().keySet()
				.containsAll(abstracted.getInVars().keySet()) : "Abstraction should not read more variables";
		assert constrainingVars
				.containsAll(abstracted.getInVars().keySet()) : "Abstraction should only read constrained variables";

		assert TransFormulaUtils.checkImplication(utf, abstracted, mMscript) != LBool.SAT : "not an abstraction";

		return abstracted;
	}

}
