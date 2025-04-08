package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

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
	private final ArrayList<Constraint> mConstraints = new ArrayList<>();
	private final ArrayList<Arc> mArcs = new ArrayList<>();
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
		final HashSet<Variable> assignableVars = new HashSet<>(variables.getOutVars().values());
		assignableVars.addAll(variables.getAuxVars().values());

		final ArrayList<BooleanTerm> constraints = constraintTerm.getSubTerms();

		for (final BooleanTerm constraint : constraints) {
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

			for (final Variable var : assignableVars) {
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
					mConstraints.add(new Constraint(var, rhsTerm, relation));
				} else {
					mArcs.add(new Arc(var, rhsTerm, relation));
				}
				mDefinedVariables.add(var);
			}

		}

		mConstraints.sort((a, b) -> {
			return a.getVariable().getName().compareTo(b.getVariable().getName());
		});
		mArcs.sort((a, b) -> {
			return a.getDefinedVariable().getName().compareTo(b.getDefinedVariable().getName());
		});

		constraintCount = mConstraints.size() + mArcs.size();
	}

	public boolean hasConstraints() {
		return constraintCount > 0;
	}

	public UnmodifiableTransFormula makeGuardFormula(final ManagedScript script, final IUltimateServiceProvider service,
			final Term term, final Infeasibility infeasibility, final Collection<TermVariable> branchEncoders) {
		final HashMap<IProgramVar, TermVariable> inVars = new HashMap<>();
		for (final Entry<TermVariable, Variable> entry : mVariables.getInVars().entrySet()) {
			inVars.put(entry.getValue().getVariableTerm().programVar, entry.getKey());
		}
		final HashMap<IProgramVar, TermVariable> outVars = new HashMap<>();
		for (final Entry<TermVariable, Variable> entry : mVariables.getOutVars().entrySet()) {
			outVars.put(entry.getValue().getVariableTerm().programVar, entry.getKey());
		}

		final TransFormulaBuilder formulaBuilder = new TransFormulaBuilder(inVars, outVars, false, null,
				branchEncoders.isEmpty(), branchEncoders, false);

		final TermVariable[] freeVars = term.getFreeVars();
		// for (final TermVariable auxVar : mVariables.getAuxVars().keySet()) {
		// formulaBuilder.addAuxVar(auxVar);
		// }

		formulaBuilder.setFormula(term);
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
		for (final Constraint constraint : mConstraints) {
			if (constraint.relation == RelationSymbol.EQ) {
				updates.add(Update.getAssignmentUpdate(constraint.getVariable(), constraint.getConstraint()));
				wellDefined.add(constraint.getVariable());
			}
		}

		final HashSet<Variable> dependentVars = new HashSet<>();
		propagateWellDefined(wellDefined, dependentVars, updates);

		// All remaining variables have to be havoced, or depend on a variable that has to be havoced.

		final HashMap<IProgramVar, Variable> inProgVars = Util.map(inVars, (var) -> {
			return Map.entry(var.getVariableTerm().programVar, var);
		}, new HashMap<>());

		final HashMap<IProgramVar, Variable> outProgVars = Util.map(mVariables.getOutVars().values(), (var) -> {
			return Map.entry(var.getVariableTerm().programVar, var);
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

		propagateWellDefined(wellDefined, dependentVars, updates);

		/*
		 * If a variable is not well defined but not dependent on variables that aren't well defined, it can be havoced
		 * at will. Such a variable would also not have any other variables that depend on it, as any arc var_a < var_b
		 * would lead to an arc var_b > var_a when initially solving BinaryRelations.
		 */

		final HashMap<Variable, HashSet<Constraint>> restrictionsConstraint = new HashMap<>();
		final HashMap<Variable, HashSet<Arc>> restrictionsArc = new HashMap<>();
		for (final Constraint constraint : mConstraints) {
			if (wellDefined.contains(constraint.getVariable())) {
				continue;
			}
			if (dependentVars.contains(constraint.getVariable())) {
				continue;
			}

			final HashSet<Constraint> constraintSet = restrictionsConstraint.getOrDefault(constraint.getVariable(),
					new HashSet<>());
			constraintSet.add(constraint);
			restrictionsConstraint.put(constraint.getVariable(), constraintSet);
		}
		for (final Arc arc : mArcs) {
			if (wellDefined.contains(arc.getDefinedVariable())) {
				continue;
			}
			if (dependentVars.contains(arc.getDefinedVariable())) {
				continue;
			}

			final HashSet<Arc> arcSet = restrictionsArc.getOrDefault(arc.getDefinedVariable(), new HashSet<>());
			arcSet.add(arc);
			restrictionsArc.put(arc.getDefinedVariable(), arcSet);
		}
		final Set<Variable> independentVars = restrictionsConstraint.keySet();
		independentVars.addAll(restrictionsArc.keySet());
		for (final Variable independentVar : independentVars) {
			updates.add(Update.getHavocUpdate(independentVar,
					restrictionsConstraint.getOrDefault(independentVar, new HashSet<>()),
					restrictionsArc.getOrDefault(independentVar, new HashSet<>())));
			wellDefined.add(independentVar);
		}

		propagateWellDefined(wellDefined, dependentVars, updates);

		// TODO Take care of outVars that depend on other outVars

		updateCache = new Update[updates.size()];

		return Util.fillArray(updates, updateCache);
	}

	// get all updates that are well defined in the form wellDefinedVar = Term(const, ..., wellDefinedVar, ...)

	private void propagateWellDefined(final HashSet<Variable> wellDefined, final HashSet<Variable> dependentVars,
			final ArrayList<Update> updates) {
		boolean unchanged = false;
		while (!unchanged) {
			unchanged = true;
			for (final Arc arc : mArcs) {
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
			for (final Constraint constraint : mConstraints) {
				out.append(constraint.toString()).append("\n");
			}

			for (final Arc arc : mArcs) {
				out.append(arc.toString()).append("\n");
			}
		}

		return out.toString().stripTrailing();
	}
}
