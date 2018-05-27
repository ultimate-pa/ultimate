/*
 * Copyright (C) 2018 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ChcToBoogie plug-in.
 *
 * The ChcToBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ChcToBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ChcToBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ChcToBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ChcToBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.chctoboogie;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.lib.models.BasePayloadContainer;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.DefaultLocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.treeautomizer.HCSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.treeautomizer.HornAnnot;
import de.uni_freiburg.informatik.ultimate.lib.treeautomizer.HornClause;
import de.uni_freiburg.informatik.ultimate.lib.treeautomizer.HornClausePredicateSymbol;
import de.uni_freiburg.informatik.ultimate.lib.treeautomizer.HornUtilConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieDeclarations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Term2Expression;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TypeSortTranslator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class ChcToBoogieObserver implements IUnmanagedObserver {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	private Unit mBoogieUnit;

	private final Term2Expression mTerm2Expression;
	private HornClausePredicateSymbol mBottomPredSym;
	private String mNameOfMainEntryPointProc;
	private final ManagedScript mManagedScript;
	private final TypeSortTranslator mTypeSortTanslator;
	private HCSymbolTable mHcSymbolTable;

	public ChcToBoogieObserver(final ILogger logger, final IUltimateServiceProvider services) {
			//final ManagedScript managedScript) {
		mLogger = logger;
		mServices = services;

		mManagedScript = null;

		mTypeSortTanslator = new TypeSortTranslator(Collections.emptySet(),
				mManagedScript.getScript(), mServices);


		final BoogieDeclarations boogieDeclarations = null;//new BoogieDeclarations(unit, logger);
		final Boogie2SmtSymbolTable boogie2SmtSymbolTable = new Boogie2SmtSymbolTable(boogieDeclarations,
				mManagedScript, mTypeSortTanslator);

		mTerm2Expression = new Term2Expression(mTypeSortTanslator, boogie2SmtSymbolTable, mManagedScript);
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {
		// no initialization needed
	}

	@Override
	public void finish() throws Throwable {
		// not needed
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

	public IElement getModel() {
		return mBoogieUnit;
//		return mResult;
	}

	@Override
	public boolean process(final IElement root) throws Exception {
		final BasePayloadContainer rootNode = (BasePayloadContainer) root;

		final Map<String, IAnnotations> st = rootNode.getPayload().getAnnotations();
		final HornAnnot annot = (HornAnnot) st.get(HornUtilConstants.HORN_ANNOT_NAME);
		mLogger.debug(annot.getAnnotationsAsMap().get(HornUtilConstants.HORN_ANNOT_NAME));


		final List<HornClause> hornClausesRaw =
				(List<HornClause>) annot.getAnnotationsAsMap().get(HornUtilConstants.HORN_ANNOT_NAME);
		mHcSymbolTable = annot.getSymbolTable();

		mBottomPredSym = mHcSymbolTable.getFalseHornClausePredicateSymbol();

		final HashRelation<HornClausePredicateSymbol, HornClause> hornClauseHeadPredicateToHornClauses =
				new HashRelation<>();


		for (final HornClause hc : hornClausesRaw) {
			if (hc.isHeadFalse()) {
				hornClauseHeadPredicateToHornClauses.addPair(mBottomPredSym, hc);
			} else {
				hornClauseHeadPredicateToHornClauses.addPair(hc.getHeadPredicate(), hc);
			}
		}


		generateBoogieAst(hornClauseHeadPredicateToHornClauses);



		return true;
	}

	private void generateBoogieAst(
			final HashRelation<HornClausePredicateSymbol, HornClause> hornClauseHeadPredicateToHornClauses) {

		final List<Declaration> declarations = new ArrayList<>();
		final DefaultLocation loc = new DefaultLocation();

		for (final HornClausePredicateSymbol headPredSymbol : hornClauseHeadPredicateToHornClauses.getDomain()) {


			List<Statement> nondetSwitch = null;
			final List<VariableDeclaration> localVarDecs = null;

			for (final HornClause hornClause : hornClauseHeadPredicateToHornClauses.getImage(headPredSymbol)) {

				final List<Statement> branchBody = new ArrayList<>();
				final Statement assume =
						new AssumeStatement(loc, mTerm2Expression.translate(hornClause.getConstraintFormula()));
				branchBody.add(assume);

				for (int i = 0; i < hornClause.getNoBodyPredicates(); i++) {
					final HornClausePredicateSymbol bodyPredSym = hornClause.getBodyPredicates().get(i);
					final List<Term> bodyPredArgs = hornClause.getBodyPredToArgs().get(i);

//					for (final Term bpa : bodyPredArgs) {
//						for (final TermVariable fv : bpa.getFreeVars()) {
//
//						}
//					}
					updateLocalVarDecs(localVarDecs, bodyPredArgs);

					final CallStatement call = new CallStatement(loc, false, null, predSymToMethodName(bodyPredSym),
							bodyPredArgs.stream().map(t -> mTerm2Expression.translate(t)).collect(Collectors.toList())
								.toArray(new Expression[bodyPredArgs.size()]));
					branchBody.add(call);
				}

				nondetSwitch = addIteBranch(loc, nondetSwitch, branchBody);
			}

			final VarList[] inParams = getInParamsForHeadPredSymbol(loc, headPredSymbol);


			final VariableDeclaration[] localVars;
			{

				localVars = localVarDecs.toArray(new VariableDeclaration[localVarDecs.size()]);
			}

			final Statement[] block = nondetSwitch.toArray(new Statement[nondetSwitch.size()]);
			final Body body = new Body(loc, localVars, block);

			final Procedure proc =
					new Procedure(loc, null, predSymToMethodName(headPredSymbol), null,
							inParams, new VarList[0],
							null, body);
			declarations.add(proc);
		}

		// add the main entry point
		declarations.add(constructMainEntryPointProcedure(loc));

		mBoogieUnit = new Unit(loc,
				declarations.toArray(new Declaration[declarations.size()]));
	}

	private void updateLocalVarDecs(final List<VariableDeclaration> localVarDecs, final List<Term> bodyPredArgs) {
		for (final Term bpa : bodyPredArgs) {
			for (final TermVariable fv : bpa.getFreeVars()) {

			}
		}

	}

	/**
	 * For each procedure we create here, the inParams are determined by the signature of the HornClausePredicateSymbol
	 * that is associated with the procedure.
	 * This methods computes those inParams in the right format.
	 *
	 * @param loc
	 * @param headPredSym
	 * @return
	 */
	private VarList[] getInParamsForHeadPredSymbol(final DefaultLocation loc,
			final HornClausePredicateSymbol headPredSym) {

		final VarList[] result = new VarList[headPredSym.getArity()];

		for (int i = 0; i < headPredSym.getArity(); i++) {
			final Sort sort = headPredSym.getParameterSorts().get(i);
			final ASTType correspondingType = getCorrespondingAstType(loc, sort);
			final String varName = getHeadVarName(i, sort);
			final VarList vl = new VarList(loc, new String[] { varName }, correspondingType);
			result[i] = vl;
		}

		return result;
	}

	private ASTType getCorrespondingAstType(final ILocation loc, final Sort sort) {
		if (sort.getName().equals("Int")) {
			return new PrimitiveType(loc, BoogieType.TYPE_INT, "int");
		} else if (sort.getName().equals("Real")) {
			return new PrimitiveType(loc, BoogieType.TYPE_REAL, "real");
		} else if (sort.getName().equals("Bool")) {
			return new PrimitiveType(loc, BoogieType.TYPE_BOOL, "bool");
		} else {
			throw new AssertionError("case not implemented");

		}
	}

	private String getHeadVarName(final int i, final Sort sort) {
		return mHcSymbolTable.getHeadVarName(i, sort);
	}

	private Declaration constructMainEntryPointProcedure(final ILocation loc) {

		final Statement callToBottomProc = new CallStatement(loc, false, null, predSymToMethodName(mBottomPredSym),
				new Expression[0]);

		final Statement assertFalse = new AssertStatement(loc,
				ExpressionFactory.createBooleanLiteral(loc, false));

		final Body body = new Body(loc, new VariableDeclaration[0],
				new Statement[] {
						callToBottomProc,
						assertFalse
				});

		return new Procedure(loc, null, mNameOfMainEntryPointProc, null, new VarList[0], new VarList[0], null, body);
	}

	private List<Statement> addIteBranch(final ILocation loc, final List<Statement> nondetSwitch,
			final List<Statement> branchBody) {
		if (nondetSwitch == null) {
			return branchBody;
		} else if (nondetSwitch.size() == 1 && nondetSwitch.get(0) instanceof IfStatement) {
			final Statement[] oldIfStm = new Statement[] { nondetSwitch.remove(0)};

			final Statement newIfStm = new IfStatement(loc,
					ExpressionFactory.constructBooleanWildCardExpression(loc),
					oldIfStm,
					branchBody.toArray(new Statement[branchBody.size()]));

			return Collections.singletonList(newIfStm);
		} else {
			assert nondetSwitch.get(0) instanceof AssumeStatement || nondetSwitch.get(0) instanceof CallStatement;
			final Statement newIfStm = new IfStatement(loc,
					ExpressionFactory.constructBooleanWildCardExpression(loc),
					nondetSwitch.toArray(new Statement[nondetSwitch.size()]),
					branchBody.toArray(new Statement[nondetSwitch.size()]));

			return Collections.singletonList(newIfStm);
		}
	}

	private String predSymToMethodName(final HornClausePredicateSymbol predSym) {
		return predSym.getName();

	}
}
