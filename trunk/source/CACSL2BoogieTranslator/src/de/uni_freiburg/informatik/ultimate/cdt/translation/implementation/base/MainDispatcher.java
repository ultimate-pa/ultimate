/*
 * Copyright (C) 2015 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Stefan Wissert
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

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

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
import org.eclipse.cdt.core.dom.ast.IASTExpressionList;
import org.eclipse.cdt.core.dom.ast.IASTExpressionStatement;
import org.eclipse.cdt.core.dom.ast.IASTFieldReference;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTGotoStatement;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTIfStatement;
import org.eclipse.cdt.core.dom.ast.IASTInitializerList;
import org.eclipse.cdt.core.dom.ast.IASTLabelStatement;
import org.eclipse.cdt.core.dom.ast.IASTLiteralExpression;
import org.eclipse.cdt.core.dom.ast.IASTNamedTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTNullStatement;
import org.eclipse.cdt.core.dom.ast.IASTParameterDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTPointer;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorElifStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorElseStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorEndifStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorErrorStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIfStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIfdefStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIfndefStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIncludeStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorMacroDefinition;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorPragmaStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorUndefStatement;
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
import org.eclipse.cdt.core.dom.ast.gnu.IGNUASTCompoundStatementExpression;
import org.eclipse.cdt.internal.core.dom.parser.IASTAmbiguousExpression;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTDesignatedInitializer;
import org.eclipse.cdt.internal.core.dom.parser.cpp.IASTAmbiguousCondition;

import de.uni_freiburg.informatik.ultimate.cdt.decorator.DecoratedUnit;
import de.uni_freiburg.informatik.ultimate.cdt.decorator.DecoratorNode;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CHandlerTranslationResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.IACSLHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ACSLProblemNode;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ACSLResultExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Assigns;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.AtLabelExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CastExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CodeAnnot;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Contract;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Ensures;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.FieldAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.FreeableExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopAnnot;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopAssigns;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopInvariant;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopVariant;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.MallocableExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.NullPointer;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.OldValueExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Requires;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ValidExpression;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.witness.ExtractedGhostUpdate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.witness.ExtractedWitnessInvariant;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.witness.IExtractedCorrectnessWitness;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.witness.IExtractedWitnessDeclaration;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 */
public class MainDispatcher implements IDispatcher {

	/**
	 * The current decorator tree.
	 */
	private DecoratorNode mDecoratorTree;
	/**
	 * The iterator for the current decorator tree.
	 */
	private Iterator<DecoratorNode> mDecoratorTreeIterator;
	/**
	 * Temp variable for next ACSL calculation.
	 */
	private DecoratorNode mNextACSLBuffer;

	private final IExtractedCorrectnessWitness mWitness;

	private final CHandler mCHandler;
	private final ITypeHandler mTypeHandler;
	private final LocationFactory mLocationFactory;
	private final ILogger mLogger;
	private final PreprocessorHandler mPreprocessorHandler;
	private final IACSLHandler mAcslHandler;
	private IASTNode mAcslHook;
	private final TranslationSettings mSettings;

	public MainDispatcher(final ILogger logger, final IExtractedCorrectnessWitness witness,
			final LocationFactory locFac, final ITypeHandler typeHandler, final CHandler cHandler,
			final PreprocessorHandler preprocessorHandler, final IACSLHandler acslHandler,
			final TranslationSettings settings) {
		mLogger = logger;
		mWitness = witness;
		mLocationFactory = locFac;
		mTypeHandler = typeHandler;
		mCHandler = cHandler;
		mPreprocessorHandler = preprocessorHandler;
		mAcslHandler = acslHandler;
		mSettings = settings;
	}

	@Override
	public CHandlerTranslationResult dispatch(final List<DecoratedUnit> nodes) {
		assert !nodes.isEmpty();
		return mCHandler.visit(this, nodes);
	}

	@Override
	public Result dispatch(final IASTNode n) {
		final Result result = switch (n) {
		case final IASTTranslationUnit tu -> mCHandler.visit(this, tu);
		case final IASTSimpleDeclaration decl -> mCHandler.visit(this, decl);
		case final IASTParameterDeclaration decl -> mCHandler.visit(this, decl);
		case final IASTASMDeclaration decl -> mCHandler.visit(this, decl);
		case final IASTDeclarator decl -> mCHandler.visit(this, decl);
		case final IASTFunctionDefinition fun -> mCHandler.visit(this, fun);
		case final IASTReturnStatement ret -> mCHandler.visit(this, ret);
		case final IASTSwitchStatement sw -> mCHandler.visit(this, sw);
		case final IASTWhileStatement whl -> mCHandler.visit(this, whl);
		case final IASTLabelStatement label -> mCHandler.visit(this, label);
		case final IASTNullStatement nul -> mCHandler.visit(this, nul);
		case final IASTContinueStatement cont -> mCHandler.visit(this, cont);
		case final IASTDeclarationStatement decl -> mCHandler.visit(this, decl);
		case final IASTDefaultStatement def -> mCHandler.visit(this, def);
		case final IASTDoStatement d -> mCHandler.visit(this, d);
		case final IASTExpressionStatement exSt -> mCHandler.visit(this, exSt);
		case final IASTForStatement forSt -> mCHandler.visit(this, forSt);
		case final IASTGotoStatement gt -> mCHandler.visit(this, gt);
		case final IASTIfStatement ifSt -> mCHandler.visit(this, ifSt);
		case final IASTCompoundStatement com -> mCHandler.visit(this, com);
		case final IASTBreakStatement br -> mCHandler.visit(this, br);
		case final IASTCaseStatement cs -> mCHandler.visit(this, cs);
		case final IASTEqualsInitializer eq -> mCHandler.visit(this, eq);
		case final CASTDesignatedInitializer di -> mCHandler.visit(this, di);
		case final IASTInitializerList init -> mCHandler.visit(this, init);
		case final IASTLiteralExpression lit -> mCHandler.visit(this, lit);
		case final IASTIdExpression id -> mCHandler.visit(this, id);
		case final IASTFunctionCallExpression call -> mCHandler.visit(this, call);
		case final IASTFieldReference ref -> mCHandler.visit(this, ref);
		case final IASTExpressionList exLs -> mCHandler.visit(this, exLs);
		case final IASTConditionalExpression cond -> mCHandler.visit(this, cond);
		case final IASTCastExpression cs -> mCHandler.visit(this, cs);
		case final IASTBinaryExpression bin -> mCHandler.visit(this, bin);
		case final IASTBinaryTypeIdExpression btie -> mCHandler.visit(this, btie);
		case final IASTArraySubscriptExpression arSub -> mCHandler.visit(this, arSub);
		case final IASTAmbiguousExpression amEx -> mCHandler.visit(this, amEx);
		case final IASTAmbiguousCondition amC -> mCHandler.visit(this, amC);
		case final IASTTypeIdExpression tie -> mCHandler.visit(this, tie);
		case final IASTTypeIdInitializerExpression tiie -> mCHandler.visit(this, tiie);
		case final IASTUnaryExpression un -> mCHandler.visit(this, un);
		case final IGNUASTCompoundStatementExpression comp -> mCHandler.visit(this, comp);
		case final IASTPointer pointer -> mCHandler.visit(this, pointer);
		// Call TypeHandler for declaration and type specifiers
		case final IASTSimpleDeclSpecifier decl -> mTypeHandler.visit(this, decl);
		case final IASTNamedTypeSpecifier nts -> mTypeHandler.visit(this, nts);
		case final IASTEnumerationSpecifier ets -> mTypeHandler.visit(this, ets);
		case final IASTElaboratedTypeSpecifier ets -> mTypeHandler.visit(this, ets);
		case final IASTCompositeTypeSpecifier cts -> mTypeHandler.visit(this, cts);
		// error -> we will cancel the translation anyway ...
		case final IASTProblemStatement problem -> mCHandler.visit(this, problem);
		case final IASTProblemExpression problem -> mCHandler.visit(this, problem);
		case final IASTProblemDeclaration problem -> mCHandler.visit(this, problem);
		case final IASTProblem problem -> mCHandler.visit(this, problem);
		case final IASTProblemTypeId problem -> mCHandler.visit(this, problem);
		// no specific handling for those types
		default -> mCHandler.visit(this, n);
		};
		return transformWithWitness(n, result);
	}

	/**
	 * Transform the given {@code result} with the witness entries found at {@code node}.
	 *
	 * @param node
	 *            The node where the witness entries should be matched.
	 * @param result
	 *            The result to be transformed.
	 * @return The result transformed by the witness.
	 */
	private Result transformWithWitness(final IASTNode node, final Result result) {
		if (mWitness == null) {
			return result;
		}
		final Set<ExtractedWitnessInvariant> matchedWitnessInvariants = mWitness.getInvariants(node);
		final List<ExtractedGhostUpdate> matchedGhostUpdates = mWitness.getGhostUpdates(node);
		if (matchedWitnessInvariants.isEmpty() && matchedGhostUpdates.isEmpty()) {
			return result;
		}
		if (!(result instanceof ExpressionResult)) {
			mLogger.warn("Unable to annotate " + node.getRawSignature() + " with a witness entry");
			return result;
		}
		ExpressionResult rtr = (ExpressionResult) result;
		final ILocation loc = mLocationFactory.createCLocation(node);
		// Ensure that invariants are evaluated before the ghost variables are updated and that the order of ghost
		// updates is preserved. Therefore iterate over these objects in reverse order.
		for (int i = matchedGhostUpdates.size() - 1; i >= 0; i--) {
			rtr = matchedGhostUpdates.get(i).transform(loc, this, rtr, mSettings.checkWitnesses());
		}
		for (final ExtractedWitnessInvariant entry : matchedWitnessInvariants) {
			rtr = entry.transform(loc, this, rtr, mSettings.checkWitnesses());
		}
		return rtr;
	}

	@Override
	public Result dispatch(final ACSLNode n) {
		return dispatch(n, mAcslHook);
	}

	@Override
	public Result dispatch(final ACSLNode n, final IASTNode cHook) {
		mAcslHook = cHook;
		return switch (n) {
		case final CodeAnnot codeAnnot -> mAcslHandler.visit(this, codeAnnot);
		case final BinaryExpression bin -> mAcslHandler.visit(this, bin);
		case final UnaryExpression unary -> mAcslHandler.visit(this, unary);
		case final ArrayAccessExpression arrayAccess -> mAcslHandler.visit(this, arrayAccess);
		case final BooleanLiteral boolLit -> mAcslHandler.visit(this, boolLit);
		case final CastExpression cast -> mAcslHandler.visit(this, cast);
		case final IntegerLiteral intLit -> mAcslHandler.visit(this, intLit);
		case final RealLiteral realLit -> mAcslHandler.visit(this, realLit);
		case final ValidExpression valid -> mAcslHandler.visit(this, valid);
		case final FreeableExpression free -> mAcslHandler.visit(this, free);
		case final MallocableExpression malloc -> mAcslHandler.visit(this, malloc);
		case final ACSLResultExpression result -> mAcslHandler.visit(this, result);
		case final FieldAccessExpression fieldAccess -> mAcslHandler.visit(this, fieldAccess);
		case final OldValueExpression old -> mAcslHandler.visit(this, old);
		case final AtLabelExpression at -> mAcslHandler.visit(this, at);
		case final IdentifierExpression id -> mAcslHandler.visit(this, id);
		case final IfThenElseExpression ite -> mAcslHandler.visit(this, ite);
		case final QuantifierExpression quantifier -> mAcslHandler.visit(this, quantifier);
		case final Contract contract -> mAcslHandler.visit(this, contract);
		case final Requires requires -> mAcslHandler.visit(this, requires);
		case final Ensures ensures -> mAcslHandler.visit(this, ensures);
		case final Assigns assigns -> mAcslHandler.visit(this, assigns);
		case final LoopInvariant loopInv -> mAcslHandler.visit(this, loopInv);
		case final LoopVariant looopVar -> mAcslHandler.visit(this, looopVar);
		case final LoopAssigns loopAss -> mAcslHandler.visit(this, loopAss);
		case final LoopAnnot loopAnnot -> mAcslHandler.visit(this, loopAnnot);
		case final NullPointer np -> mAcslHandler.visit(this, np);
		case final ACSLProblemNode problem -> mAcslHandler.visit(this, problem);
		default -> mAcslHandler.visit(this, n);
		};
	}

	public void updateDecoratorTreeAndIterator(final DecoratorNode node) {
		mDecoratorTree = node;
		mDecoratorTreeIterator = mDecoratorTree.iterator();
	}

	@Override
	public NextACSL nextACSLStatement() {
		DecoratorNode current;
		if (mNextACSLBuffer != null) {
			current = mNextACSLBuffer;
			mNextACSLBuffer = null;
		} else {
			if (!mDecoratorTreeIterator.hasNext()) {
				return null;
			}
			current = mDecoratorTreeIterator.next();
		}
		while (mDecoratorTreeIterator.hasNext() && current.getAcslNode() == null) {
			// jump over C nodes.
			current = mDecoratorTreeIterator.next();
		}
		if (!mDecoratorTreeIterator.hasNext() && current.getCNode() != null) {
			return null;
		}
		// current = found ACSL node
		final ArrayList<ACSLNode> acsl = new ArrayList<>();
		checkACSLLocation(current);
		acsl.add(current.getAcslNode());
		if (!mDecoratorTreeIterator.hasNext()) {
			return new NextACSL(acsl, null);
		}
		// find successor C node with same parent as the found acsl node
		final Iterator<DecoratorNode> myIterator = mDecoratorTree.iterator();
		DecoratorNode cNode = mDecoratorTree;
		while (myIterator.hasNext() && (cNode.getAcslNode() == null || !cNode.equals(current))) {
			cNode = myIterator.next();
		}
		// both iterators are on the same node --> cNode == current
		assert cNode.equals(current);
		while (myIterator.hasNext() && cNode.getAcslNode() != null) {
			cNode = myIterator.next();
		}
		IASTNode successor;
		if (cNode.getCNode() != null && cNode.getCNode().getParent().equals(current.getParent().getCNode())) {
			successor = cNode.getCNode();
		} else {
			successor = null;
		}

		DecoratorNode nextNode = mDecoratorTreeIterator.next();
		// block of ACSL nodes
		while (mDecoratorTreeIterator.hasNext() && nextNode.getCNode() == null) {
			// check parent of acsl nodes to be equivalent
			if (!current.getParent().getCNode().equals(nextNode.getParent().getCNode())) {
				// parent changed! not one block!
				assert mNextACSLBuffer == null;
				if (nextNode.getAcslNode() != null) {
					mNextACSLBuffer = nextNode;
				}
				return new NextACSL(acsl, successor);
			}
			checkACSLLocation(nextNode);
			acsl.add(nextNode.getAcslNode());
			nextNode = mDecoratorTreeIterator.next();
		}
		if (nextNode.getAcslNode() != null && current.getParent().getCNode().equals(nextNode.getParent().getCNode())) {
			acsl.add(nextNode.getAcslNode());
		} else if (nextNode.getAcslNode() != null) {
			mNextACSLBuffer = nextNode;
		}
		return new NextACSL(acsl, successor);
	}

	@Override
	public IASTNode getAcslHook() {
		return mAcslHook;
	}

	@Override
	public Result dispatch(final IASTPreprocessorStatement n) {
		return switch (n) {
		case final IASTPreprocessorElifStatement elif -> mPreprocessorHandler.visit(this, elif);
		case final IASTPreprocessorElseStatement els -> mPreprocessorHandler.visit(this, els);
		case final IASTPreprocessorEndifStatement endif -> mPreprocessorHandler.visit(this, endif);
		case final IASTPreprocessorErrorStatement error -> mPreprocessorHandler.visit(this, error);
		case final IASTPreprocessorIfdefStatement ifdef -> mPreprocessorHandler.visit(this, ifdef);
		case final IASTPreprocessorIfndefStatement indef -> mPreprocessorHandler.visit(this, indef);
		case final IASTPreprocessorIfStatement ifSt -> mPreprocessorHandler.visit(this, ifSt);
		case final IASTPreprocessorIncludeStatement incl -> mPreprocessorHandler.visit(this, incl);
		case final IASTPreprocessorMacroDefinition macro -> mPreprocessorHandler.visit(this, macro);
		case final IASTPreprocessorPragmaStatement pragma -> mPreprocessorHandler.visit(this, pragma);
		case final IASTPreprocessorUndefStatement undef -> mPreprocessorHandler.visit(this, undef);
		default -> mPreprocessorHandler.visit(this, n);
		};
	}

	/**
	 * Parent node of an ACSL node should be a decorator node containing C. The C node should be instance of
	 * IASTCompoundStatement or IASTTranslationUnit.<br>
	 * <b>ACSL is unexpected in other locations.</b>
	 *
	 * @param acslNode
	 *            the ACSL holding decorator node that should be checked.
	 */
	private static void checkACSLLocation(final DecoratorNode acslNode) {
		if (acslNode.getAcslNode() == null) {
			throw new IllegalArgumentException(
					"The given decorator node is not holding ACSL" + acslNode.getCNode().getRawSignature());
		}
		if (acslNode.getParent().getCNode() == null) {
			throw new IllegalArgumentException(
					"The parent node of the given ACSL holding decorator node is not a C node!");
		}
		if (!(acslNode.getParent().getCNode() instanceof IASTTranslationUnit)
				&& !(acslNode.getParent().getCNode() instanceof IASTCompoundStatement)) {
			throw new IllegalArgumentException("The location of the given ACSL holding decorator node is unexpected!");
		}
	}

	@Override
	public List<ACSLNode> getFunctionContractFromWitness(final IASTNode node) {
		if (mWitness == null) {
			return List.of();
		}
		return mWitness.getFunctionContracts(node).stream().flatMap(x -> x.getAcslContractClauses().stream())
				.collect(Collectors.toList());
	}

	@Override
	public Set<IExtractedWitnessDeclaration> getWitnessDeclarations() {
		return mWitness == null ? Set.of() : mWitness.getGlobalDeclarations();
	}
}
