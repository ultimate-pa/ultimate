package de.uni_freiburg.informatik.ultimate.plugins.chctoboogie;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcPredicateSymbol;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcVar;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClause;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class GenerateBoogieAst {

	Unit mResult;
	private final GenerateBoogieAstHelper mHelper;

	public GenerateBoogieAst(final HashRelation<HcPredicateSymbol, HornClause> hornClauseHeadPredicateToHornClauses,
			final GenerateBoogieAstHelper helper) {
		mHelper = helper;

		mResult = generateBoogieAst(hornClauseHeadPredicateToHornClauses);
	}

	private Unit generateBoogieAst(
			final HashRelation<HcPredicateSymbol, HornClause> hornClauseHeadPredicateToHornClauses) {

		final ILocation loc = mHelper.getLoc();
		final List<Declaration> declarations = new ArrayList<>();

		final Deque<HcPredicateSymbol> headPredQueue = new ArrayDeque<>();
		final Set<HcPredicateSymbol> addedToQueueBefore = new HashSet<>();

		headPredQueue.push(mHelper.getBottomPredSym());
		addedToQueueBefore.add(mHelper.getBottomPredSym());

		while (!headPredQueue.isEmpty()) {
			// breadth-first (pollFirst) or depth-first (pop) should not matter here
			final HcPredicateSymbol headPredSymbol = headPredQueue.pop();

			final Set<HornClause> hornClausesForHeadPred = hornClauseHeadPredicateToHornClauses.getImage(headPredSymbol);

			final Set<HcVar> allBodyPredVariables = new HashSet<>();

			final List<Statement> nondetSwitch =
					generateNondetSwitchForPred(loc, hornClausesForHeadPred, headPredQueue,
							addedToQueueBefore, allBodyPredVariables);

			final VarList[] inParams = mHelper.getInParamsForHeadPredSymbol(loc, headPredSymbol, hornClausesForHeadPred.isEmpty());


			final List<VariableDeclaration> localVarDecs = new ArrayList<>();
			mHelper.updateLocalVarDecs(localVarDecs, allBodyPredVariables, loc);

			final VariableDeclaration[] localVars;
			{
				localVars = localVarDecs == null
						? new VariableDeclaration[0]
						: localVarDecs.toArray(new VariableDeclaration[localVarDecs.size()]);
			}

			/*
			 * Note: in the headPredUnconstrained case, the procedure body must consist of one "assume false;"
			 *  statement.
			 * General intuition: Each procedure blocks execution on those input vectors where the model of the
			 *  corresponding predicate is false. A predicate that does not occur in a head, can be set to false
			 *   everywhere.
			 */
			assert hornClausesForHeadPred.isEmpty() || !nondetSwitch.stream().anyMatch(Objects::isNull);
			final Statement[] block = hornClausesForHeadPred.isEmpty() ?
					new Statement[] { new AssumeStatement(loc, ExpressionFactory.createBooleanLiteral(loc, false)) }:
					nondetSwitch.toArray(new Statement[nondetSwitch.size()]);
			final Body body = new Body(loc, localVars, block);

			final Procedure proc =
					new Procedure(loc, new Attribute[0], mHelper.predSymToMethodName(headPredSymbol), new String[0],
							inParams, new VarList[0],
							new Specification[0], body);
			declarations.add(proc);
		}

		// add the main entry point
		declarations.add(constructMainEntryPointProcedure(loc));

		declarations.addAll(mHelper.getDeclarationsForSkolemFunctions());

		return new Unit(loc,
				declarations.toArray(new Declaration[declarations.size()]));
	}

	/**
	 *
	 * @param loc
	 * @param predSymbolToLabel null if non-goto mode
	 * @param predLabelToNumber
	 * @param hornClausesForHeadPred
	 * @param headPredQueue (updated)
	 * @param addedToQueueBefore (updated)
	 * @param allBodyPredVariables (updated)
	 * @return
	 */
	private List<Statement> generateNondetSwitchForPred(final ILocation loc,
			final Set<HornClause> hornClausesForHeadPred,
			final Deque<HcPredicateSymbol> headPredQueue, final Set<HcPredicateSymbol> addedToQueueBefore,
			final Set<HcVar> allBodyPredVariables) {
		/*
		 * create the procedure body according to all Horn clauses with headPredSymbol as their head
		 */
		List<Statement> nondetSwitch = null;

		for (final HornClause hornClause : hornClausesForHeadPred) {
			if (SmtUtils.isFalseLiteral(hornClause.getConstraintFormula())) {
				// branch with an "assume false" --> can be skipped
				continue;
			}

			allBodyPredVariables.addAll(hornClause.getBodyVariables());

			final List<Statement> branchBody = new ArrayList<>();
			final Statement assume =
					new AssumeStatement(loc, mHelper.translate(hornClause.getConstraintFormula()));
			branchBody.add(assume);

			for (int i = 0; i < hornClause.getNoBodyPredicates(); i++) {
				final HcPredicateSymbol bodyPredSym = hornClause.getBodyPredicates().get(i);
				final List<Term> bodyPredArgs = hornClause.getBodyPredToArgs().get(i);

				if (!addedToQueueBefore.contains(bodyPredSym)) {
					headPredQueue.push(bodyPredSym);
					addedToQueueBefore.add(bodyPredSym);
				}

				final List<Expression> translatedArguments =
						bodyPredArgs.stream().map(t -> mHelper.translate(t)).collect(Collectors.toList());

				final CallStatement call = new CallStatement(loc, false, new VariableLHS[0],
						mHelper.predSymToMethodName(bodyPredSym),
						translatedArguments.toArray(new Expression[bodyPredArgs.size()]));
				branchBody.add(call);
			}

			nondetSwitch = mHelper.addIteBranch(loc, nondetSwitch, branchBody,
				ExpressionFactory.constructBooleanWildCardExpression(loc));
		}
		return nondetSwitch;
	}

	public Unit getResult() {
		return mResult;
	}

	private Declaration constructMainEntryPointProcedure(final ILocation loc) {

		Statement[] statements;

		final Statement callToBottomProc = new CallStatement(loc, false, new VariableLHS[0],
				mHelper.predSymToMethodName(mHelper.getBottomPredSym()), new Expression[0]);

		final Statement assertFalse = new AssertStatement(loc,
				ExpressionFactory.createBooleanLiteral(loc, false));

		statements = new Statement[] { callToBottomProc, assertFalse };

		final Body body = new Body(loc, new VariableDeclaration[0], statements);

		return new Procedure(loc, new Attribute[0], mHelper.getNameOfMainEntryPointProc(), new String[0],
				new VarList[0], new VarList[0], new Specification[0], body);
	}

}
