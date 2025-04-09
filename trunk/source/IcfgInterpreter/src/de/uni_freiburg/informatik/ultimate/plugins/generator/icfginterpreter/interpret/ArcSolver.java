package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.BinaryEqualityRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.BinaryNumericRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.BinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.BooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ReturnType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.AndTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.NotTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.OrTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.VariableTerm;

public class ArcSolver {
	private final VariableSet mVariables;
	private final HashSet<Variable> mDefinedVariables;
	private final HashMap<Variable, ArrayList<Constraint>> mConstraints = new HashMap<>();
	private final HashMap<Variable, ArrayList<Arc>> mArcs = new HashMap<>();
	private final int constraintCount;
	// private final BooleanTerm guardTerm;

	/**
	 * @param outVars
	 * @param inVars
	 * @param variables
	 * @param service
	 * @param theory
	 * @param theory
	 * @param constraintList should be an {@link AndTerm} from {@link OrTerm#getSubTerms()} of an OrTerm created by
	 *                       {@link TermNormalizer#simplifyToDNF(BooleanTerm)}
	 * @param mAllVariables
	 */
	public ArcSolver(final AndTerm constraintTerm, final ManagedScript managedScript, final VariableSet variables,
			final Theory theory) {

		mVariables = variables;
		mDefinedVariables = new HashSet<>();

		for (final BooleanTerm constraint : constraintTerm.getSubTerms()) {
			final HashSet<Variable> containedOutVars = Util.filter(constraint.getVariables(), (var) -> {
				final VariableTerm varTerm = var.getVariableTerm();
				return (varTerm.isOutVar || varTerm.isAuxVar) && !varTerm.isInVar;
			});

			if (containedOutVars.isEmpty()) {
				continue;
				// does not constrain next state variables, may only be a guard
			}

			BinaryRelation binRel;
			if (constraint.getSubTerms().get(0).returnType == ReturnType.Int) {
				binRel = BinaryNumericRelation.convert(constraint.toSMTTerm(theory));
			} else {
				binRel = BinaryEqualityRelation.convert(constraint.toSMTTerm(theory));
			}

			for (final Variable var : mVariables.getVariables()) {
				if (var.getVariableTerm().isInVar) {
					// We do not need to solve equations for InVars, they are a known constant in a transition.
					continue;
				}
				final Term termVar = var.getTerm().toSMTTerm(theory);
				final SolvedBinaryRelation solvedBinEQ = binRel.solveForSubject(managedScript.getScript(), termVar);
				if (solvedBinEQ == null) {
					continue;
				}
				final Term definition = solvedBinEQ.getRightHandSide();
				RelationSymbol relation = solvedBinEQ.getRelationSymbol();
				if (definition == null) {
					continue;
				}
				ExecutionTerm rhsTerm = IcfgTranslation.parseTerm(definition, variables).simplify();
				if (rhsTerm.returnType == ReturnType.Boolean && relation == RelationSymbol.DISTINCT) {
					// bool_x != bool_y would become the update havoc(bool_x, "!= bool_y")
					// but we can just simplify to bool_x = !(bool_y) to get an assignment update set(bool_x, !bool_y)
					rhsTerm = new NotTerm((BooleanTerm) rhsTerm);
					relation = RelationSymbol.EQ;
				}
				if (rhsTerm.getVariables().size() == 0) {
					final ArrayList<Constraint> varConstraints = mConstraints.getOrDefault(var, new ArrayList<>());
					varConstraints.add(new Constraint(var, rhsTerm, relation));
					mConstraints.put(var, varConstraints);
				} else {
					final ArrayList<Arc> varArcs = mArcs.getOrDefault(var, new ArrayList<>());
					varArcs.add(new Arc(var, rhsTerm, relation));
					mArcs.put(var, varArcs);
				}
				mDefinedVariables.add(var);
			}

		}

		for (final ArrayList<Constraint> constraints : mConstraints.values()) {
			constraints.sort((a, b) -> {
				return a.getVariable().getName().compareTo(b.getVariable().getName());
			});
		}
		for (final ArrayList<Arc> arcs : mArcs.values()) {
			arcs.sort((a, b) -> {
				return a.getDefinedVariable().getName().compareTo(b.getDefinedVariable().getName());
			});
		}

		constraintCount = mConstraints.size() + mArcs.size();
	}

	public boolean hasConstraints() {
		return constraintCount > 0;
	}

	public UnmodifiableTransFormula makeGuardFormula(final ManagedScript script, final IUltimateServiceProvider service,
			ExecutionTerm term, final Infeasibility infeasibility, final Collection<TermVariable> branchEncoders) {

		final HashMap<IProgramVar, TermVariable> inVars = new HashMap<>();
		for (final Entry<TermVariable, Variable> entry : mVariables.getInVars().entrySet()) {
			inVars.put(entry.getValue().getVariableTerm().mProgramVar, entry.getKey());
		}
		final HashMap<IProgramVar, TermVariable> outVars = new HashMap<>();
		for (final Entry<TermVariable, Variable> entry : mVariables.getOutVars().entrySet()) {
			outVars.put(entry.getValue().getVariableTerm().mProgramVar, entry.getKey());
		}

		final TransFormulaBuilder formulaBuilder = new TransFormulaBuilder(inVars, outVars, false, null,
				branchEncoders.isEmpty(), branchEncoders, false);

		final Theory theory = script.getScript().getTheory();

		for (final Entry<TermVariable, Variable> entry : mVariables.getAuxVars().entrySet()) {
			final TermVariable auxVar = entry.getValue().getVariableTerm().toDistinctSmtTerm(theory);

			final Variable newVar = entry.getValue().replaceTermVariable(auxVar);
			term = term.replaceTerm(entry.getValue().getTerm(), newVar.getTerm());
			formulaBuilder.addAuxVar(auxVar);
		}

		final Term smtTerm = term.toSMTTerm(theory);

		formulaBuilder.setFormula(smtTerm);
		formulaBuilder.setInfeasibility(infeasibility);
		final UnmodifiableTransFormula subTermFormula = formulaBuilder.finishConstruction(script);
		return TransFormulaUtils.computeGuard(subTermFormula, script, service);
	}

	private Update[] updateCache = null;

	public Update[] makeUpdates() {
		if (updateCache != null) {
			return updateCache.clone();
		}

		final ArrayList<Update> updates = new ArrayList<>();

		final Collection<Variable> inVars = mVariables.getInVars().values();
		final HashSet<Variable> wellDefined = new HashSet<>(inVars);

		// get all updates that are in the form wellDefinedVar = Term(const, const, ...)
		for (final Entry<Variable, ArrayList<Constraint>> entry : mConstraints.entrySet()) {
			for (final Constraint constraint : entry.getValue()) {
				if (constraint.relation == RelationSymbol.EQ) {
					updates.add(Update.getAssignmentUpdate(entry.getKey(), constraint.getConstraint()));
					wellDefined.add(entry.getKey());
				}
			}
		}

		eliminateAuxVar(wellDefined);
		final HashSet<Variable> dependentVars = new HashSet<>();
		propagateWellDefined(wellDefined, dependentVars, updates);

		// All remaining variables have to be havoced, or depend on a variable that has to be havoced.

		final HashMap<IProgramVar, Variable> inProgVars = Util.map(inVars, (var) -> {
			return Map.entry(var.getVariableTerm().mProgramVar, var);
		}, new HashMap<>());

		final HashMap<IProgramVar, Variable> outProgVars = Util.map(mVariables.getOutVars().values(), (var) -> {
			return Map.entry(var.getVariableTerm().mProgramVar, var);
		}, new HashMap<>());

		// Make updates for variables that are not defined in the next state (havoc any value), this happens when:
		// A. The OutVars do not contain a variable that is in the InVars.
		// B. A variable of the OutVars does not appear in the InVars or the term.
		for (final Entry<IProgramVar, Variable> inVar : inProgVars.entrySet()) {
			if (outProgVars.containsKey(inVar.getKey())) {
				// The program variable has a defining term variable in the next state
				continue;
			}
			updates.add(Update.getHavocUpdateAny(inVar.getKey(), inVar.getValue().getTerm().returnType));
			wellDefined.add(inVar.getValue());
		}

		for (final Entry<IProgramVar, Variable> outVar : outProgVars.entrySet()) {
			if (mDefinedVariables.contains(outVar.getValue()) || inProgVars.containsKey(outVar.getKey())) {
				// The TermVariable has some constraint in the term or is constant (inVar and outVar)
				continue;
			}
			updates.add(Update.getHavocUpdateAny(outVar.getValue()));
			wellDefined.add(outVar.getValue());
		}

		eliminateAuxVar(wellDefined);
		propagateWellDefined(wellDefined, dependentVars, updates);

		/*
		 * If a variable is not well defined but not dependent on variables that aren't well defined, it can be havoced
		 * at will. Such a variable would also not have any other variables that depend on it, as any arc var_a < var_b
		 * would lead to an arc var_b > var_a when initially solving BinaryRelations.
		 */

		final HashSet<Variable> independentVars = Util.filter(mVariables.getVariables(), (variable) -> {
			return !(wellDefined.contains(variable) || dependentVars.contains(variable)
					|| mVariables.getAuxVars().containsValue(variable));
		});

		for (final Variable independentVar : independentVars) {
			updates.add(
					Update.getHavocUpdate(independentVar, mConstraints.getOrDefault(independentVar, new ArrayList<>()),
							mArcs.getOrDefault(independentVar, new ArrayList<>())));
			wellDefined.add(independentVar);
		}

		eliminateAuxVar(wellDefined);
		propagateWellDefined(wellDefined, dependentVars, updates);

		// TODO Take care of outVars that depend on other outVars

		updateCache = new Update[updates.size()];

		return Util.fillArray(updates, updateCache);
	}

	private void replaceAuxWithValue(final Variable varToReplace, final ExecutionTerm replacement) {
		for (final Variable variable : mDefinedVariables) {
			final ArrayList<Arc> arcs = mArcs.getOrDefault(variable, new ArrayList<>());
			for (int i = 0; i < arcs.size(); i++) {
				final Arc arc = arcs.get(i);
				final ExecutionTerm newConstraint = arc.getConstraint().replaceTerm(varToReplace.getTerm(),
						replacement);
				arcs.set(i, new Arc(variable, newConstraint, arc.relation));
			}
			final ArrayList<Constraint> constraints = mConstraints.getOrDefault(variable, new ArrayList<>());
			for (int i = 0; i < constraints.size(); i++) {
				final Constraint constraint = constraints.get(i);
				final ExecutionTerm newConstraint = constraint.getConstraint().replaceTerm(varToReplace.getTerm(),
						replacement);
				constraints.set(i, new Constraint(variable, newConstraint, constraint.relation));
			}
		}
	}

	public void eliminateAuxVar(final HashSet<Variable> wellDefined) {
		boolean unchanged = false;
		while (!unchanged) {
			unchanged = true;
			for (final Variable variable : mVariables.getAuxVars().values()) {
				for (final Constraint constraint : mConstraints.getOrDefault(variable, new ArrayList<>())) {
					if (constraint.relation.equals(RelationSymbol.EQ)
							&& wellDefined.containsAll(constraint.getConstraint().getVariables())) {
						// replace the AuxVar with its definition in every other arc and constraint
						replaceAuxWithValue(variable, constraint.getConstraint());
						wellDefined.add(variable);
						unchanged = false;
						break;
					}
				}
			}
		}
	}

	// get all updates that are well defined in the form wellDefinedVar = Term(const, ..., wellDefinedVar, ...)
	private void propagateWellDefined(final HashSet<Variable> wellDefined, final HashSet<Variable> dependentVars,
			final ArrayList<Update> updates) {
		boolean unchanged = false;
		while (!unchanged) {
			unchanged = true;
			for (final Variable variable : mDefinedVariables) {
				if (wellDefined.contains(variable) || variable.getVariableTerm().isAuxVar) {
					continue;
				}
				for (final Arc arc : mArcs.getOrDefault(variable, new ArrayList<>())) {
					if (wellDefined.contains(arc.getDefinedVariable())) {
						continue;
					}
					if (arc.relation != RelationSymbol.EQ) {
						continue;
					}
					if (!wellDefined.containsAll(arc.getVariables())) {
						dependentVars.add(arc.getDefinedVariable());
						continue;
					}
					// this variable is equal to a term that only contains well defined variables
					updates.add(Update.getAssignmentUpdate(arc.getDefinedVariable(), arc.getConstraint()));
					unchanged = false;
					wellDefined.add(arc.getDefinedVariable());
					dependentVars.remove(arc.getDefinedVariable());
				}
			}

		}
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof ArcSolver)) {
			return false;
		}
		final ArcSolver bCast = (ArcSolver) b;

		return mConstraints.equals(bCast.mConstraints) && mArcs.equals(bCast.mArcs)
				&& mVariables.equals(bCast.mVariables);
	}

	@Override
	public String toString() {
		final StringBuilder out = new StringBuilder();

		if (constraintCount == 0) {
			out.append("No constraints on the next state.");
		} else {
			for (final Variable variable : mDefinedVariables) {
				for (final Constraint constraint : mConstraints.getOrDefault(variable, new ArrayList<>())) {
					out.append(constraint.toString()).append("\n");
				}

				for (final Arc arc : mArcs.getOrDefault(variable, new ArrayList<>())) {
					out.append(arc.toString()).append("\n");
				}
			}
		}

		return out.toString().stripTrailing();
	}
}
