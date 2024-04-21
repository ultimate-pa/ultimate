package de.uni_freiburg.informatik.ultimate.btorutils;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class AssignmentRule {
	public DebugIdentifier assignmentLocationIdentifier;
	public IProgramVar lhs;
	public Term rhs;
	public TransFormula tf;

	public AssignmentRule(final DebugIdentifier assignmentLocationIdentifier, final IProgramVar lhs, final Term rhs,
			final TransFormula tf) {
		this.assignmentLocationIdentifier = assignmentLocationIdentifier;
		this.lhs = lhs;
		this.rhs = rhs;
		this.tf = tf;
	}

	public static List<AssignmentRule> getAssignmentsFromTransition(final DebugIdentifier assignmentLocationIdentifier,
			final TransFormula tf, final ManagedScript script) {
		final List<AssignmentRule> assignmentRules = new ArrayList<>();
		final Set<IProgramVar> assignedVars = TransFormulaUtils.computeAssignedVars(tf.getInVars(), tf.getOutVars());
		for (final IProgramVar assignedVar : assignedVars) {
			boolean foundAssignment = false;
			if (!(tf.getOutVars().containsKey(assignedVar))) {
				continue;
			}
			if (tf.isHavocedOut(assignedVar)) {
				assignmentRules.add(new AssignmentRule(assignmentLocationIdentifier, assignedVar,
						script.getScript().term("true"), tf));
			} else {
				final Term formula = tf.getFormula();
				if (formula instanceof ApplicationTerm) {
					final ApplicationTerm appFormula = (ApplicationTerm) formula;
					if (appFormula.getFunction().getName().equals("and")) {
						for (final Term possibleAssignment : appFormula.getParameters()) {
							if (possibleAssignment instanceof ApplicationTerm) {
								final ApplicationTerm appPossibleAssignment = (ApplicationTerm) possibleAssignment;
								if (appPossibleAssignment.getFunction().getName().equals("=")) {
									final Term lhsTerm = appPossibleAssignment.getParameters()[0];
									final Term rhsTerm = appPossibleAssignment.getParameters()[1];
									if (lhsTerm instanceof TermVariable) {
										final TermVariable lhsVar = (TermVariable) lhsTerm;
										if (TransFormulaUtils.getProgramVarForTerm(tf, lhsVar).equals(assignedVar)) {
											assignmentRules.add(new AssignmentRule(assignmentLocationIdentifier,
													assignedVar, appPossibleAssignment.getParameters()[1], tf));
											foundAssignment = true;
											break;
										}
									}
									if (rhsTerm instanceof TermVariable) {
										final TermVariable rhsVar = (TermVariable) rhsTerm;
										if (TransFormulaUtils.getProgramVarForTerm(tf, rhsVar).equals(assignedVar)) {
											assignmentRules.add(new AssignmentRule(assignmentLocationIdentifier,
													assignedVar, appPossibleAssignment.getParameters()[0], tf));
											foundAssignment = true;
											break;
										}
									}
								}
							}

						}
					} else if (SmtUtils.isAtomicFormula(appFormula)) {
						if (appFormula.getFunction().getName().equals("=")) {
							final Term lhsTerm = appFormula.getParameters()[0];
							if (lhsTerm instanceof TermVariable) {
								final TermVariable lhsVar = (TermVariable) lhsTerm;
								if (TransFormulaUtils.getProgramVarForTerm(tf, lhsVar).equals(assignedVar)) {
									assignmentRules.add(new AssignmentRule(assignmentLocationIdentifier, assignedVar,
											appFormula.getParameters()[1], tf));
									foundAssignment = true;
								}
							}
							final Term rhsTerm = appFormula.getParameters()[1];
							if (rhsTerm instanceof TermVariable) {
								final TermVariable rhsVar = (TermVariable) rhsTerm;
								if (TransFormulaUtils.getProgramVarForTerm(tf, rhsVar).equals(assignedVar)) {
									assignmentRules.add(new AssignmentRule(assignmentLocationIdentifier, assignedVar,
											appFormula.getParameters()[0], tf));
									foundAssignment = true;
								}
							}
						}
					} else {
						throw new UnsupportedOperationException("Transformula not in cnf");

					}
					if (!foundAssignment) {
						throw new UnsupportedOperationException("Transformula variable has no assignment");
					}
				}
			}
		}
		return assignmentRules;
	}

	public BtorExpression getRHSAsExpression(final Map<String, BtorExpression> variableMap) {
		return TermToBtorUtil.convertRHSToBtorExpression(rhs, tf, variableMap);
	}
}
