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
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm.ReturnType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.AndTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.OrTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

public class ArcSolver {
	private final HashMap<TermVariable, Variable> mVariables;
	private final HashSet<Variable> mOutVars;
	private final HashSet<Variable> mInVars;
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
	public ArcSolver(final AndTerm constraintTerm, final ManagedScript managedScript,
			final HashMap<TermVariable, Variable> variables, final HashSet<Variable> inVars,
			final HashSet<Variable> outVars, final IUltimateServiceProvider service, final Theory theory) {
		mVariables = variables;
		mOutVars = outVars;
		mInVars = inVars;

		final ArrayList<BooleanTerm> constraints = constraintTerm.getSubTerms();

		final HashMap<TermVariable, Variable> smtConvertedVariables = new HashMap<>();
		for (final Variable var : variables.values()) {
			smtConvertedVariables.put((TermVariable) var.getTerm().toSMTTerm(theory), var);
		}

		for (final BooleanTerm constraint : constraints) {
			final HashSet<Variable> containedOutVars = Util.filter(constraint.getVariables(), (var) -> {
				return var.getVariableTerm().isOutVar && !var.getVariableTerm().isInVar;
			});

			if (containedOutVars.isEmpty()) {
				continue;
				// does not constrain next state variables, perhaps only a guard
			}

			BinaryRelation binRel;
			if (constraint.getSubTerms().get(0).returnType == ReturnType.Int) {
				binRel = BinaryNumericRelation.convert(constraint.toSMTTerm(theory));
			} else {
				binRel = BinaryEqualityRelation.convert(constraint.toSMTTerm(theory));
			}

			for (final Variable var : mOutVars) {
				final Term termVar = var.getTerm().toSMTTerm(theory);
				final SolvedBinaryRelation solvedBinEQ = binRel.solveForSubject(managedScript.getScript(), termVar);
				if (solvedBinEQ == null) {
					continue;
				}
				final Term definition = solvedBinEQ.getRightHandSide();
				final RelationSymbol relation = solvedBinEQ.getRelationSymbol();
				if (definition == null) {
					continue;
				}
				final ExecutionTerm rhsTerm = TermNormalizer.parseTerm(definition, smtConvertedVariables).simplify();
				if (rhsTerm.getVariables().size() == 0) {
					mConstraints.add(new Constraint(var, rhsTerm, relation));
				} else {
					mArcs.add(new Arc(var, rhsTerm, relation));
				}
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
		for (final Variable inVar : mInVars) {
			inVars.put(inVar.getVariableTerm().programVar, inVar.getVariableTerm().termvar);
		}
		final HashMap<IProgramVar, TermVariable> outVars = new HashMap<>();
		for (final Variable outVar : mOutVars) {
			outVars.put(outVar.getVariableTerm().programVar, outVar.getVariableTerm().termvar);
		}
		final HashSet<TermVariable> auxVars = new HashSet<>();
		for (final Variable var : mVariables.values()) {
			if (var.getVariableTerm().isAuxVar) {
				auxVars.add(var.getVariableTerm().termvar);
			}
		}

		final TransFormulaBuilder formulaBuilder = new TransFormulaBuilder(inVars, outVars, false, null,
				branchEncoders.isEmpty(), branchEncoders, false);

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

		final HashSet<Variable> wellDefined = Util.copySet(mInVars);
		final HashSet<Variable> mentionedVars = new HashSet<>();

		// get all updates that are in the form wellDefinedVar = Term(const, const, ...)
		for (final Constraint constraint : mConstraints) {
			mentionedVars.add(constraint.getVariable());
			if (constraint.relation == RelationSymbol.EQ) {
				updates.add(Update.getAssignmentUpdate(constraint.getVariable(), constraint.getConstraint()));
				wellDefined.add(constraint.getVariable());
			}
		}

		// get all updates that are well defined in the form wellDefinedVar = Term(const, ..., wellDefinedVar, ...)
		final HashSet<Variable> dependentVars = new HashSet<>();
		boolean unchanged = false;
		while (!unchanged) {
			unchanged = true;
			for (final Arc arc : mArcs) {
				mentionedVars.add(arc.getDefinedVariable());
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

		// All remaining variables have to be havoced, or depend on a variable that has to be havoced.

		final HashMap<IProgramVar, Variable> inProgVars = Util.map(mInVars, (var) -> {
			return Map.entry(var.getVariableTerm().programVar, var);
		}, new HashMap<>());

		final HashMap<IProgramVar, Variable> outProgVars = Util.map(mOutVars, (var) -> {
			return Map.entry(var.getVariableTerm().programVar, var);
		}, new HashMap<>());
		// Make updates for variables that are not defined in the next state (havoc any value), this happens when:
		// A. The OutVars do not contain a variable that is in the InVars. TODO is this actually correct?
		// B. A variable of the OutVars does not appear in the InVars or the term.

		for (final Entry<IProgramVar, Variable> inVar : inProgVars.entrySet()) {
			if (outProgVars.containsKey(inVar.getKey())) {
				// The program variable has a defining term variable in the next state
				continue;
			}
			updates.add(Update.getHavocUpdateAny(inVar.getKey(), inVar.getValue().getTerm().returnType));
		}

		for (final Entry<IProgramVar, Variable> outVar : outProgVars.entrySet()) {
			if (mentionedVars.contains(outVar.getValue()) || inProgVars.containsKey(outVar.getKey())) {
				// The TermVariable has some constraint in the term or is constant (inVar and outVar)
				continue;
			}
			updates.add(Update.getHavocUpdateAny(outVar.getValue()));
		}

		/*
		 * If a variable is not well defined but not dependent on other variables, it can be havoced at will. Such a
		 * variable would also not have any other variables that depend on it, as any arc var_a < var_b would lead to an
		 * arc var_b > var_a when initially solving BinaryRelations.
		 */

		for (final Constraint constraint : mConstraints) {
			if (wellDefined.contains(constraint.getVariable())) {
				continue;
			}
			if (dependentVars.contains(constraint.getVariable())) {
				continue;
			}

			updates.add(
					Update.getHavocUpdate(constraint.getVariable(), constraint.getConstraint(), constraint.relation));
			wellDefined.add(constraint.getVariable());
		}

		// TODO Take care of outVars that depend on other outVars

		updateCache = new Update[updates.size()];

		return Util.fillArray(updates, updateCache);
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
