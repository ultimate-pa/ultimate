package de.uni_freiburg.informatik.ultimate.btorutils;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Expression2Term.IIdentifierTranslator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;

public class AssignmentRule {
	public DebugIdentifier assignmentLocationIdentifier;
	public IProgramVar lhs;
	public Expression rhs;
	public TransFormula tf;
	public BtorExpression guard;
	Boogie2SMT boogie2SMT;

	public AssignmentRule(final DebugIdentifier assignmentLocationIdentifier, final IProgramVar lhs,
			final Expression rhs, final TransFormula tf, final BtorExpression guard, final Boogie2SMT boogie2SMT) {
		this.assignmentLocationIdentifier = assignmentLocationIdentifier;
		this.lhs = lhs;
		this.rhs = rhs;
		this.tf = tf;
		this.guard = guard;
		this.boogie2SMT = boogie2SMT;
	}

	public static List<AssignmentRule> getAssignmentsFromTransition(final DebugIdentifier assignmentLocationIdentifier,
			final IcfgEdge icfgEdge, final ManagedScript script, final BtorExpression guard,
			final Boogie2SMT boogie2SMT) {
		final List<AssignmentRule> assignmentRules = new ArrayList<>();
		// extract statements from edge
		if (icfgEdge instanceof StatementSequence) {
			final List<Statement> statements = ((StatementSequence) icfgEdge).getStatements();
			for (final Statement statement : statements) {
				// assignement statements are separated into lhs and rhs
				if (statement instanceof AssignmentStatement) {
					final AssignmentStatement assignmentStatement = (AssignmentStatement) statement;
					final Expression[] rightHandSides = assignmentStatement.getRhs();
					final LeftHandSide[] leftHandSides = assignmentStatement.getLhs();
					assert (rightHandSides.length == leftHandSides.length);
					// add a new assignment rule for each lhs-rhs pair
					for (int i = 0; i < leftHandSides.length; i++) {
						if (leftHandSides[i] instanceof VariableLHS) {
							final VariableLHS lhs = (VariableLHS) leftHandSides[i];
							final IProgramVar assignedVar = boogie2SMT.getBoogie2SmtSymbolTable()
									.getBoogieVar(lhs.getIdentifier(), lhs.getDeclarationInformation(), false);
							assignmentRules.add(new AssignmentRule(assignmentLocationIdentifier, assignedVar,
									rightHandSides[i], icfgEdge.getTransformula(), guard, boogie2SMT));
						}
					}
				} else if (statement instanceof HavocStatement) {
					final HavocStatement havocStatement = (HavocStatement) statement;
					final LeftHandSide[] leftHandSides = havocStatement.getIdentifiers();
					// add a new assignment rule with null rhs for each havoced variable
					for (final LeftHandSide leftHandSide : leftHandSides) {
						if (leftHandSide instanceof VariableLHS) {
							final VariableLHS lhs = (VariableLHS) leftHandSide;
							final IProgramVar assignedVar = boogie2SMT.getBoogie2SmtSymbolTable()
									.getBoogieVar(lhs.getIdentifier(), lhs.getDeclarationInformation(), false);
							assignmentRules.add(new AssignmentRule(assignmentLocationIdentifier, assignedVar, null,
									icfgEdge.getTransformula(), guard, boogie2SMT));
						}
					}
				}
			}
		}
		return assignmentRules;

	}

	// convert rhs of an assignment rule to a btor expression
	public BtorExpression getRHSAsExpression(final Map<String, BtorExpression> variableMap) {
		final BtorSort sort = new BtorSort(lhs.getSort());

		if (rhs != null) {
			final IIdentifierTranslator[] its = { boogie2SMT.new LocalVarAndGlobalVarTranslator(),
					boogie2SMT.createConstOnlyIdentifierTranslator() };
			// first convert expression to SMT term, then use TermToBtorUtil to obtain the btor expression
			final BtorExpression btorexpression = TermToBtorUtil.convertRhsToBtorExpression(
					boogie2SMT.getExpression2Term().translateToTerm(its, rhs).term(), tf, variableMap, sort,
					boogie2SMT);
			return btorexpression;
		} else {
			// null rhs assignement rules are havoc statements and thus have btor expression type INPUT
			return new BtorExpression(sort, "havoc_" + assignmentLocationIdentifier + "_" + lhs.getGloballyUniqueId(),
					true);
		}

	}
}
