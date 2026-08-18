/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.util.List;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.IASTASMDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTArraySubscriptExpression;
import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTBinaryTypeIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTBreakStatement;
import org.eclipse.cdt.core.dom.ast.IASTCaseStatement;
import org.eclipse.cdt.core.dom.ast.IASTCastExpression;
import org.eclipse.cdt.core.dom.ast.IASTCompositeTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
import org.eclipse.cdt.core.dom.ast.IASTConditionalExpression;
import org.eclipse.cdt.core.dom.ast.IASTContinueStatement;
import org.eclipse.cdt.core.dom.ast.IASTDeclarationStatement;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTDefaultStatement;
import org.eclipse.cdt.core.dom.ast.IASTDoStatement;
import org.eclipse.cdt.core.dom.ast.IASTElaboratedTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTEnumerationSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTEqualsInitializer;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTExpressionList;
import org.eclipse.cdt.core.dom.ast.IASTExpressionStatement;
import org.eclipse.cdt.core.dom.ast.IASTFieldReference;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTGotoStatement;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTIfStatement;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTInitializerList;
import org.eclipse.cdt.core.dom.ast.IASTLabelStatement;
import org.eclipse.cdt.core.dom.ast.IASTLiteralExpression;
import org.eclipse.cdt.core.dom.ast.IASTNamedTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTNullStatement;
import org.eclipse.cdt.core.dom.ast.IASTParameterDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTPointer;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorStatement;
import org.eclipse.cdt.core.dom.ast.IASTProblem;
import org.eclipse.cdt.core.dom.ast.IASTProblemDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTProblemExpression;
import org.eclipse.cdt.core.dom.ast.IASTProblemStatement;
import org.eclipse.cdt.core.dom.ast.IASTProblemTypeId;
import org.eclipse.cdt.core.dom.ast.IASTReturnStatement;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTSwitchStatement;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.IASTTypeIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTTypeIdInitializerExpression;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTWhileStatement;
import org.eclipse.cdt.core.dom.ast.c.ICASTDesignatedInitializer;
import org.eclipse.cdt.core.dom.ast.gnu.IGNUASTCompoundStatementExpression;
import org.eclipse.cdt.internal.core.dom.parser.IASTAmbiguousExpression;
import org.eclipse.cdt.internal.core.dom.parser.cpp.IASTAmbiguousCondition;

import de.uni_freiburg.informatik.ultimate.cdt.decorator.DecoratedUnit;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CHandlerTranslationResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.SkipResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.witness.ExtractedFunctionContract;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.witness.IExtractedWitnessDeclaration;

public class PRDispatcher implements IDispatcher {

	private final ITypeHandler mTypeHandler;
	private final CHandler mCHandler;

	public PRDispatcher(final CHandler chandler, final LocationFactory locFac, final ITypeHandler typeHandler) {
		mTypeHandler = typeHandler;
		mCHandler = chandler;
	}

	@Override
	public CHandlerTranslationResult dispatch(final List<DecoratedUnit> nodes) {
		assert !nodes.isEmpty();
		return mCHandler.visit(this, nodes);
	}

	@Override
	public Result dispatch(final IASTNode n) {
		return switch (n) {
		case final IASTTranslationUnit tu -> mCHandler.visit(this, tu);
		case final IASTSimpleDeclaration dec -> mCHandler.visit(this, dec);
		case final IASTParameterDeclaration dec -> mCHandler.visit(this, dec);
		case final IASTProblemDeclaration problem -> mCHandler.visit(this, problem);
		case final IASTASMDeclaration dec -> mCHandler.visit(this, dec);
		case final IASTDeclarator dec -> mCHandler.visit(this, dec);
		case final IASTFunctionDefinition def -> mCHandler.visit(this, def);
		case final IASTSimpleDeclSpecifier decSpec -> mTypeHandler.visit(this, decSpec);
		case final IASTNamedTypeSpecifier nts -> mTypeHandler.visit(this, nts);
		case final IASTEnumerationSpecifier enumSpec -> mTypeHandler.visit(this, enumSpec);
		case final IASTElaboratedTypeSpecifier ets -> mTypeHandler.visit(this, ets);
		case final IASTCompositeTypeSpecifier cts -> mTypeHandler.visit(this, cts);
		case final IASTReturnStatement ret -> mCHandler.visit(this, ret);
		case final IASTSwitchStatement sw -> mCHandler.visit(this, sw);
		case final IASTWhileStatement whl -> mCHandler.visit(this, whl);
		case final IASTLabelStatement label -> mCHandler.visit(this, label);
		case final IASTNullStatement nul -> mCHandler.visit(this, nul);
		case final IASTContinueStatement cont -> mCHandler.visit(this, cont);
		case final IASTDeclarationStatement dec -> mCHandler.visit(this, dec);
		case final IASTDefaultStatement def -> mCHandler.visit(this, def);
		case final IASTDoStatement d -> mCHandler.visit(this, d);
		case final IASTExpressionStatement exprSt -> mCHandler.visit(this, exprSt);
		case final IASTForStatement forSt -> mCHandler.visit(this, forSt);
		case final IASTGotoStatement got -> mCHandler.visit(this, got);
		case final IASTIfStatement ifSt -> mCHandler.visit(this, ifSt);
		case final IASTCompoundStatement comp -> mCHandler.visit(this, comp);
		case final IASTBreakStatement brk -> mCHandler.visit(this, brk);
		case final IASTCaseStatement cs -> mCHandler.visit(this, cs);
		case final IASTProblemStatement problem -> mCHandler.visit(this, problem);
		case final IASTEqualsInitializer init -> mCHandler.visit(this, init);
		case final ICASTDesignatedInitializer init -> mCHandler.visit(this, init);
		case final IASTInitializerList init -> mCHandler.visit(this, init);
		case final IASTLiteralExpression lit -> mCHandler.visit(this, lit);
		case final IASTIdExpression id -> mCHandler.visit(this, id);
		case final IASTFunctionCallExpression call -> mCHandler.visit(this, call);
		case final IASTFieldReference ref -> mCHandler.visit(this, ref);
		case final IASTExpressionList exprLs -> mCHandler.visit(this, exprLs);
		case final IASTConditionalExpression cond -> mCHandler.visit(this, cond);
		case final IASTCastExpression cast -> mCHandler.visit(this, cast);
		case final IASTBinaryExpression bin -> mCHandler.visit(this, bin);
		case final IASTBinaryTypeIdExpression btie -> mCHandler.visit(this, btie);
		case final IASTArraySubscriptExpression arraySub -> mCHandler.visit(this, arraySub);
		case final IASTAmbiguousExpression amb -> mCHandler.visit(this, amb);
		case final IASTAmbiguousCondition amb -> mCHandler.visit(this, amb);
		case final IASTTypeIdExpression tie -> mCHandler.visit(this, tie);
		case final IASTTypeIdInitializerExpression tiie -> mCHandler.visit(this, tiie);
		case final IASTUnaryExpression unary -> mCHandler.visit(this, unary);
		case final IASTProblemExpression problem -> mCHandler.visit(this, problem);
		case final IGNUASTCompoundStatementExpression comp -> mCHandler.visit(this, comp);
		case final IASTExpression expr -> mCHandler.visit(this, expr);
		case final IASTProblem problem -> mCHandler.visit(this, problem);
		case final IASTInitializerClause init -> mCHandler.visit(this, init);
		case final IASTPointer pointer -> mCHandler.visit(this, pointer);
		case final IASTProblemTypeId problem -> mCHandler.visit(this, problem);
		default -> mCHandler.visit(this, n);
		};
	}

	@Override
	public Result dispatch(final IASTPreprocessorStatement node) {
		return new SkipResult();
	}

	@Override
	public Result dispatch(final ACSLNode node, final IASTNode cHook) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Result dispatch(final ACSLNode node) {
		throw new UnsupportedOperationException();
	}

	@Override
	public IASTNode getAcslHook() {
		throw new UnsupportedOperationException();
	}

	@Override
	public NextACSL nextACSLStatement() {
		throw new UnsupportedOperationException();
	}

	@Override
	public Set<ExtractedFunctionContract> getFunctionContractFromWitness(final IASTNode node) {
		return Set.of();
	}

	@Override
	public Set<IExtractedWitnessDeclaration> getWitnessDeclarations() {
		return Set.of();
	}
}
