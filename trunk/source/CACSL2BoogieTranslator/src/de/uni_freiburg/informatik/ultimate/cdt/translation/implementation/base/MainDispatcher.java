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

import java.text.ParseException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.IASTASMDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTArrayDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTArrayModifier;
import org.eclipse.cdt.core.dom.ast.IASTArraySubscriptExpression;
import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTBinaryTypeIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTBreakStatement;
import org.eclipse.cdt.core.dom.ast.IASTCaseStatement;
import org.eclipse.cdt.core.dom.ast.IASTCastExpression;
import org.eclipse.cdt.core.dom.ast.IASTComment;
import org.eclipse.cdt.core.dom.ast.IASTCompositeTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
import org.eclipse.cdt.core.dom.ast.IASTConditionalExpression;
import org.eclipse.cdt.core.dom.ast.IASTContinueStatement;
import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTDeclarationListOwner;
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
import org.eclipse.cdt.core.dom.ast.IASTFieldDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTFieldReference;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTFunctionStyleMacroParameter;
import org.eclipse.cdt.core.dom.ast.IASTGotoStatement;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTIfStatement;
import org.eclipse.cdt.core.dom.ast.IASTImplicitName;
import org.eclipse.cdt.core.dom.ast.IASTImplicitNameOwner;
import org.eclipse.cdt.core.dom.ast.IASTInitializer;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTInitializerList;
import org.eclipse.cdt.core.dom.ast.IASTLabelStatement;
import org.eclipse.cdt.core.dom.ast.IASTLiteralExpression;
import org.eclipse.cdt.core.dom.ast.IASTName;
import org.eclipse.cdt.core.dom.ast.IASTNamedTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTNullStatement;
import org.eclipse.cdt.core.dom.ast.IASTParameterDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTPointer;
import org.eclipse.cdt.core.dom.ast.IASTPointerOperator;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorElifStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorElseStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorEndifStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorErrorStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIfStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIfdefStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIfndefStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIncludeStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorMacroDefinition;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorMacroExpansion;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorObjectStyleMacroDefinition;
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
import org.eclipse.cdt.core.dom.ast.IASTStandardFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IASTSwitchStatement;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.IASTTypeId;
import org.eclipse.cdt.core.dom.ast.IASTTypeIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTTypeIdInitializerExpression;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTWhileStatement;
import org.eclipse.cdt.internal.core.dom.parser.IASTAmbiguousExpression;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTDesignatedInitializer;
import org.eclipse.cdt.internal.core.dom.parser.cpp.IASTAmbiguousCondition;

import de.uni_freiburg.informatik.ultimate.acsl.parser.ACSLSyntaxErrorException;
import de.uni_freiburg.informatik.ultimate.acsl.parser.Parser;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.cdt.decorator.DecoratedUnit;
import de.uni_freiburg.informatik.ultimate.cdt.decorator.DecoratorNode;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CHandlerTranslationResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionListResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.IACSLHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ACSLResultExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ACSLType;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Assertion;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Assigns;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Assumes;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.AtLabelExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Axiomatic;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BaseAddrExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Behavior;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BitVectorAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BlockLengthExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Case;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CastExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CodeAnnot;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CodeForBehavior;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CodeInvariant;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CodeStatement;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Completeness;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Contract;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ContractStatement;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Decreases;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Ensures;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.FieldAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.FreeableExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.GlobalInvariant;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.GlobalLTLInvariant;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Inductive;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Invariant;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Lemma;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LogicFunction;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LogicStatement;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopAnnot;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopAssigns;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopForBehavior;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopInvariant;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopStatement;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopVariant;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.MallocableExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ModelVariable;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.NotDefinedExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.NullPointer;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.OldValueExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Parameter;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.PolyIdentifier;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Predicate;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Requires;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.SizeOfExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.SyntacticNamingExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Terminates;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.TypeInvariant;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ValidExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.WildcardExpression;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.witness.ExtractedWitnessInvariant;

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

	private final Set<Set<String>> mNodeLabelsOfAddedWitnesses;

	private final Map<IASTNode, ExtractedWitnessInvariant> mWitnessInvariants;

	private final CHandler mCHandler;
	private final ITypeHandler mTypeHandler;
	private final LocationFactory mLocationFactory;
	private final ILogger mLogger;
	private final PreprocessorHandler mPreprocessorHandler;
	private final IACSLHandler mAcslHandler;
	private IASTNode mAcslHook;

	private final Deque<WitnessInvariant> mCurrentWitnessInvariants;

	public MainDispatcher(final ILogger logger, final Map<IASTNode, ExtractedWitnessInvariant> witnessInvariants,
			final LocationFactory locFac, final ITypeHandler typeHandler, final CHandler cHandler,
			final PreprocessorHandler preprocessorHandler, final IACSLHandler acslHandler) {
		mLogger = logger;
		mNodeLabelsOfAddedWitnesses = new LinkedHashSet<>();
		mWitnessInvariants = witnessInvariants;
		mLocationFactory = locFac;
		mTypeHandler = typeHandler;
		mCHandler = cHandler;
		mPreprocessorHandler = preprocessorHandler;
		mAcslHandler = acslHandler;
		mCurrentWitnessInvariants = new ArrayDeque<>();
	}

	@Override
	public CHandlerTranslationResult dispatch(final List<DecoratedUnit> nodes) {
		assert !nodes.isEmpty();
		return mCHandler.visit(this, nodes);
	}

	@Override
	public Result dispatch(final IASTNode n) {
		handleWitnessInvariantsBeforeDispatch(n);

		final Result result;
		if (n instanceof IASTTranslationUnit) {
			result = mCHandler.visit(this, (IASTTranslationUnit) n);
		} else if (n instanceof IASTSimpleDeclaration) {
			result = mCHandler.visit(this, (IASTSimpleDeclaration) n);
		} else if (n instanceof IASTParameterDeclaration) {
			result = mCHandler.visit(this, (IASTParameterDeclaration) n);
		} else if (n instanceof IASTASMDeclaration) {
			result = mCHandler.visit(this, (IASTASMDeclaration) n);
		} else if (n instanceof IASTDeclarator) {
			result = mCHandler.visit(this, (IASTDeclarator) n);
		} else if (n instanceof IASTFunctionDefinition) {
			result = mCHandler.visit(this, (IASTFunctionDefinition) n);
		} else if (n instanceof IASTDeclSpecifier) {
			// Here we decide which further Interface we want to visit, and
			// call the typeHandler
			if (n instanceof IASTSimpleDeclSpecifier) {
				result = mTypeHandler.visit(this, (IASTSimpleDeclSpecifier) n);
			} else if (n instanceof IASTNamedTypeSpecifier) {
				result = mTypeHandler.visit(this, (IASTNamedTypeSpecifier) n);
			} else if (n instanceof IASTEnumerationSpecifier) {
				result = mTypeHandler.visit(this, (IASTEnumerationSpecifier) n);
			} else if (n instanceof IASTElaboratedTypeSpecifier) {
				result = mTypeHandler.visit(this, (IASTElaboratedTypeSpecifier) n);
			} else if (n instanceof IASTCompositeTypeSpecifier) {
				result = mTypeHandler.visit(this, (IASTCompositeTypeSpecifier) n);
			} else {
				result = mCHandler.visit(this, n);
			}
		} else if (n instanceof IASTStatement) {
			if (n instanceof IASTReturnStatement) {
				result = mCHandler.visit(this, (IASTReturnStatement) n);
			} else if (n instanceof IASTSwitchStatement) {
				result = mCHandler.visit(this, (IASTSwitchStatement) n);
			} else if (n instanceof IASTWhileStatement) {
				result = mCHandler.visit(this, (IASTWhileStatement) n);
			} else if (n instanceof IASTLabelStatement) {
				result = mCHandler.visit(this, (IASTLabelStatement) n);
			} else if (n instanceof IASTNullStatement) {
				result = mCHandler.visit(this, (IASTNullStatement) n);
			} else if (n instanceof IASTContinueStatement) {
				result = mCHandler.visit(this, (IASTContinueStatement) n);
			} else if (n instanceof IASTDeclarationStatement) {
				result = mCHandler.visit(this, (IASTDeclarationStatement) n);
			} else if (n instanceof IASTDefaultStatement) {
				result = mCHandler.visit(this, (IASTDefaultStatement) n);
			} else if (n instanceof IASTDoStatement) {
				result = mCHandler.visit(this, (IASTDoStatement) n);
			} else if (n instanceof IASTExpressionStatement) {
				result = mCHandler.visit(this, (IASTExpressionStatement) n);
			} else if (n instanceof IASTForStatement) {
				result = mCHandler.visit(this, (IASTForStatement) n);
			} else if (n instanceof IASTGotoStatement) {
				result = mCHandler.visit(this, (IASTGotoStatement) n);
			} else if (n instanceof IASTIfStatement) {
				result = mCHandler.visit(this, (IASTIfStatement) n);
			} else if (n instanceof IASTCompoundStatement) {
				result = mCHandler.visit(this, (IASTCompoundStatement) n);
			} else if (n instanceof IASTBreakStatement) {
				result = mCHandler.visit(this, (IASTBreakStatement) n);
			} else if (n instanceof IASTCaseStatement) {
				result = mCHandler.visit(this, (IASTCaseStatement) n);
			} else if (n instanceof IASTProblemStatement) {
				// error -> we will cancel the translation anyway ...
				// -> should be at the end of the parent if for performance
				result = mCHandler.visit(this, (IASTProblemStatement) n);
			} else {
				result = mCHandler.visit(this, n);
			}
		} else if (n instanceof IASTInitializer) {
			if (n instanceof IASTEqualsInitializer) {
				result = mCHandler.visit(this, (IASTEqualsInitializer) n);
			} else if (n instanceof CASTDesignatedInitializer) {
				result = mCHandler.visit(this, (CASTDesignatedInitializer) n);
			} else if (n instanceof IASTInitializerList) {
				result = mCHandler.visit(this, (IASTInitializerList) n);
			} else {
				result = mCHandler.visit(this, n);
			}
		} else if (n instanceof IASTExpression) {
			if (n instanceof IASTLiteralExpression) {
				result = mCHandler.visit(this, (IASTLiteralExpression) n);
			} else if (n instanceof IASTIdExpression) {
				result = mCHandler.visit(this, (IASTIdExpression) n);
			} else if (n instanceof IASTFunctionCallExpression) {
				result = mCHandler.visit(this, (IASTFunctionCallExpression) n);
			} else if (n instanceof IASTFieldReference) {
				result = mCHandler.visit(this, (IASTFieldReference) n);
			} else if (n instanceof IASTExpressionList) {
				result = mCHandler.visit(this, (IASTExpressionList) n);
			} else if (n instanceof IASTConditionalExpression) {
				result = mCHandler.visit(this, (IASTConditionalExpression) n);
			} else if (n instanceof IASTCastExpression) {
				result = mCHandler.visit(this, (IASTCastExpression) n);
			} else if (n instanceof IASTBinaryExpression) {
				result = mCHandler.visit(this, (IASTBinaryExpression) n);
			} else if (n instanceof IASTBinaryTypeIdExpression) {
				result = mCHandler.visit(this, n);
			} else if (n instanceof IASTArraySubscriptExpression) {
				result = mCHandler.visit(this, (IASTArraySubscriptExpression) n);
			} else if (n instanceof IASTAmbiguousExpression) {
				result = mCHandler.visit(this, n);
			} else if (n instanceof IASTAmbiguousCondition) {
				result = mCHandler.visit(this, n);
			} else if (n instanceof IASTTypeIdExpression) {
				result = mCHandler.visit(this, (IASTTypeIdExpression) n);
			} else if (n instanceof IASTTypeIdInitializerExpression) {
				result = mCHandler.visit(this, (IASTTypeIdInitializerExpression) n);
			} else if (n instanceof IASTUnaryExpression) {
				result = mCHandler.visit(this, (IASTUnaryExpression) n);
			} else if (n instanceof IASTProblemExpression) {
				result = mCHandler.visit(this, (IASTProblemExpression) n);
			} else {
				result = mCHandler.visit(this, n);
			}
		} else if (n instanceof IASTArrayDeclarator) {
			result = mCHandler.visit(this, (IASTArrayDeclarator) n);
		} else if (n instanceof IASTFieldDeclarator) {
			result = mCHandler.visit(this, (IASTFieldDeclarator) n);
		} else if (n instanceof IASTInitializerClause) {
			result = mCHandler.visit(this, n);
		} else if (n instanceof IASTPointer) {
			result = mCHandler.visit(this, (IASTPointer) n);
		} else if (n instanceof IASTStandardFunctionDeclarator) {
			result = mCHandler.visit(this, (IASTStandardFunctionDeclarator) n);
		} else if (n instanceof IASTProblemDeclaration) {
			// error -> we will cancel the translation anyway ...
			// -> should be at the end of the parent if for performance
			result = mCHandler.visit(this, (IASTProblemDeclaration) n);
		} else if (n instanceof IASTProblem) {
			result = mCHandler.visit(this, (IASTProblem) n);
		} else if (n instanceof IASTProblemTypeId) {
			// error -> we will cancel the translation anyway ...
			// -> should be at the end of the parent if for performance
			result = mCHandler.visit(this, (IASTProblemTypeId) n);
		} else if (n instanceof IASTArrayModifier || n instanceof IASTComment || n instanceof IASTDeclaration
				|| n instanceof IASTDeclarationListOwner || n instanceof IASTFunctionStyleMacroParameter
				|| n instanceof IASTImplicitNameOwner || n instanceof IASTName || n instanceof IASTPointerOperator
				|| n instanceof IASTPreprocessorMacroExpansion || n instanceof IASTTypeId
				|| n instanceof IASTCompositeTypeSpecifier || n instanceof IASTPreprocessorMacroDefinition
				|| n instanceof IASTImplicitName || n instanceof IASTPreprocessorObjectStyleMacroDefinition) {
			// no specific handling for those types
			result = mCHandler.visit(this, n);
		} else {
			final String msg = "MainDispatcher: AST node type unknown: " + n.getClass();
			final ILocation loc = mLocationFactory.createCLocation(n);
			throw new UnsupportedSyntaxException(loc, msg);
		}
		handleWitnessInvariantsAfterDispatch(n, result);
		return result;
	}

	@Override
	public Result dispatch(final ACSLNode n) {
		return dispatch(n, mAcslHook);
	}

	@Override
	public Result dispatch(final ACSLNode n, final IASTNode cHook) {
		mAcslHook = cHook;
		if (n instanceof CodeAnnot) {
			return mAcslHandler.visit(this, (CodeAnnot) n);
		}
		if (n instanceof Expression) {
			if (n instanceof BinaryExpression) {
				return mAcslHandler.visit(this, (BinaryExpression) n);
			}
			if (n instanceof NotDefinedExpression) {
				return mAcslHandler.visit(this, n);
			}
			if (n instanceof UnaryExpression) {
				return mAcslHandler.visit(this, (UnaryExpression) n);
			}
			if (n instanceof ArrayAccessExpression) {
				return mAcslHandler.visit(this, (ArrayAccessExpression) n);
			}
			if (n instanceof ArrayStoreExpression) {
				return mAcslHandler.visit(this, n);
			}
			if (n instanceof BitVectorAccessExpression) {
				return mAcslHandler.visit(this, n);
			}
			if (n instanceof BooleanLiteral) {
				return mAcslHandler.visit(this, (BooleanLiteral) n);
			}
			if (n instanceof CastExpression) {
				return mAcslHandler.visit(this, (CastExpression) n);
			}
			if (n instanceof IntegerLiteral) {
				return mAcslHandler.visit(this, (IntegerLiteral) n);
			}
			if (n instanceof RealLiteral) {
				return mAcslHandler.visit(this, (RealLiteral) n);
			}
			if (n instanceof StringLiteral) {
				return mAcslHandler.visit(this, n);
			}
			if (n instanceof NullPointer) {
				return mAcslHandler.visit(this, n);
			}
			if (n instanceof ValidExpression) {
				return mAcslHandler.visit(this, (ValidExpression) n);
			}
			if (n instanceof FreeableExpression) {
				return mAcslHandler.visit(this, (FreeableExpression) n);
			}
			if (n instanceof MallocableExpression) {
				return mAcslHandler.visit(this, (MallocableExpression) n);
			}
			if (n instanceof ACSLResultExpression) {
				return mAcslHandler.visit(this, (ACSLResultExpression) n);
			}
			if (n instanceof FieldAccessExpression) {
				return mAcslHandler.visit(this, (FieldAccessExpression) n);
			}
			if (n instanceof SizeOfExpression) {
				return mAcslHandler.visit(this, n);
			}
			if (n instanceof OldValueExpression) {
				return mAcslHandler.visit(this, n);
			}
			if (n instanceof AtLabelExpression) {
				return mAcslHandler.visit(this, n);
			}
			if (n instanceof BaseAddrExpression) {
				return mAcslHandler.visit(this, n);
			}
			if (n instanceof BlockLengthExpression) {
				return mAcslHandler.visit(this, n);
			}
			if (n instanceof SyntacticNamingExpression) {
				return mAcslHandler.visit(this, n);
			}
			if (n instanceof IdentifierExpression) {
				return mAcslHandler.visit(this, (IdentifierExpression) n);
			}
			if (n instanceof FunctionApplication) {
				return mAcslHandler.visit(this, n);
			}
			if (n instanceof IfThenElseExpression) {
				return mAcslHandler.visit(this, (IfThenElseExpression) n);
			}
			if (n instanceof QuantifierExpression) {
				return mAcslHandler.visit(this, n);
			}
			if (n instanceof WildcardExpression) {
				return mAcslHandler.visit(this, n);
			}
			return mAcslHandler.visit(this, n);
		}
		if (n instanceof Contract) {
			return mAcslHandler.visit(this, (Contract) n);
		}
		if (n instanceof ContractStatement) {
			if (n instanceof Requires) {
				return mAcslHandler.visit(this, (Requires) n);
			}
			if (n instanceof Terminates) {
				return mAcslHandler.visit(this, n);
			}
			if (n instanceof Decreases) {
				return mAcslHandler.visit(this, n);
			}
			if (n instanceof Ensures) {
				return mAcslHandler.visit(this, (Ensures) n);
			}
			if (n instanceof Assigns) {
				return mAcslHandler.visit(this, (Assigns) n);
			}
			if (n instanceof Assumes) {
				return mAcslHandler.visit(this, n);
			}
			return mAcslHandler.visit(this, n);
		}
		if (n instanceof Completeness) {
			return mAcslHandler.visit(this, n);
		}
		if (n instanceof Behavior) {
			return mAcslHandler.visit(this, n);
		}
		if (n instanceof LogicStatement) {
			if (n instanceof Predicate) {
				return mAcslHandler.visit(this, n);
			}
			if (n instanceof LogicFunction) {
				return mAcslHandler.visit(this, n);
			}
			if (n instanceof Lemma) {
				return mAcslHandler.visit(this, n);
			}
			if (n instanceof Inductive) {
				return mAcslHandler.visit(this, n);
			}
			if (n instanceof Axiom) {
				return mAcslHandler.visit(this, n);
			}
			if (n instanceof Axiomatic) {
				return mAcslHandler.visit(this, n);
			}
			return mAcslHandler.visit(this, n);
		}
		if (n instanceof Invariant) {
			if (n instanceof GlobalInvariant) {
				return mAcslHandler.visit(this, n);
			}
			if (n instanceof GlobalLTLInvariant) {
				return mAcslHandler.visit(this, n);
			}
			if (n instanceof TypeInvariant) {
				return mAcslHandler.visit(this, n);
			}
			return mAcslHandler.visit(this, n);
		}
		if (n instanceof LoopStatement) {
			if (n instanceof LoopInvariant) {
				return mAcslHandler.visit(this, (LoopInvariant) n);
			}
			if (n instanceof LoopVariant) {
				return mAcslHandler.visit(this, (LoopVariant) n);
			}
			if (n instanceof LoopAssigns) {
				return mAcslHandler.visit(this, (LoopAssigns) n);
			}
			return mAcslHandler.visit(this, n);
		}
		if (n instanceof CodeStatement) {
			if (n instanceof Assertion) {
				return mAcslHandler.visit(this, n);
			}
			if (n instanceof CodeInvariant) {
				return mAcslHandler.visit(this, n);
			}
			return mAcslHandler.visit(this, n);
		}
		if (n instanceof ACSLType) {
			return mAcslHandler.visit(this, n);
		}
		if (n instanceof Case) {
			return mAcslHandler.visit(this, n);
		}
		if (n instanceof CodeForBehavior) {
			return mAcslHandler.visit(this, n);
		}
		if (n instanceof LoopAnnot) {
			return mAcslHandler.visit(this, (LoopAnnot) n);
		}
		if (n instanceof LoopForBehavior) {
			return mAcslHandler.visit(this, n);
		}
		if (n instanceof ModelVariable) {
			return mAcslHandler.visit(this, n);
		}
		if (n instanceof Parameter) {
			return mAcslHandler.visit(this, n);
		}
		if (n instanceof PolyIdentifier) {
			return mAcslHandler.visit(this, n);
		}
		return mAcslHandler.visit(this, n);
	}

	public void updateDecoratorTreeAndIterator(final DecoratorNode node) {
		mDecoratorTree = node;
		mDecoratorTreeIterator = mDecoratorTree.iterator();
	}

	@Override
	public NextACSL nextACSLStatement() throws ParseException {
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
		if (n instanceof IASTPreprocessorElifStatement) {
			return mPreprocessorHandler.visit(this, (IASTPreprocessorElifStatement) n);
		}
		if (n instanceof IASTPreprocessorElseStatement) {
			return mPreprocessorHandler.visit(this, (IASTPreprocessorElseStatement) n);
		}
		if (n instanceof IASTPreprocessorEndifStatement) {
			return mPreprocessorHandler.visit(this, (IASTPreprocessorEndifStatement) n);
		}
		if (n instanceof IASTPreprocessorErrorStatement) {
			return mPreprocessorHandler.visit(this, (IASTPreprocessorErrorStatement) n);
		}
		if (n instanceof IASTPreprocessorIfdefStatement) {
			return mPreprocessorHandler.visit(this, (IASTPreprocessorIfdefStatement) n);
		}
		if (n instanceof IASTPreprocessorIfndefStatement) {
			return mPreprocessorHandler.visit(this, (IASTPreprocessorIfndefStatement) n);
		}
		if (n instanceof IASTPreprocessorIfStatement) {
			return mPreprocessorHandler.visit(this, (IASTPreprocessorIfStatement) n);
		}
		if (n instanceof IASTPreprocessorIncludeStatement) {
			return mPreprocessorHandler.visit(this, (IASTPreprocessorIncludeStatement) n);
		}
		if (n instanceof IASTPreprocessorMacroDefinition) {
			return mPreprocessorHandler.visit(this, (IASTPreprocessorMacroDefinition) n);
		}
		if (n instanceof IASTPreprocessorPragmaStatement) {
			return mPreprocessorHandler.visit(this, (IASTPreprocessorPragmaStatement) n);
		}
		if (n instanceof IASTPreprocessorUndefStatement) {
			return mPreprocessorHandler.visit(this, (IASTPreprocessorUndefStatement) n);
		}
		return mPreprocessorHandler.visit(this, n);
	}

	@Override
	public LoopInvariantSpecification fetchInvariantAtLoop(final IASTNode node) {
		final AssertStatement as = fetchInvariantAt(node);
		LoopInvariantSpecification result;
		if (as == null) {
			result = null;
		} else {
			final ILocation loc = mLocationFactory.createCLocation(node);
			result = new LoopInvariantSpecification(loc, false, as.getFormula());
			final Check check = new Check(Check.Spec.WITNESS_INVARIANT);
			check.annotate(result);
		}
		return result;
	}

	public AssertStatement fetchInvariantAtGoto(final IASTGotoStatement node) {
		return fetchInvariantAt(node);
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

	private AssertStatement fetchInvariantAt(final IASTNode node) {
		AssertStatement result;
		if (mWitnessInvariants == null) {
			result = null;
		} else {
			final ExtractedWitnessInvariant invariants = mWitnessInvariants.get(node);
			try {
				final ILocation loc = mLocationFactory.createCLocation(node);
				final List<AssertStatement> list = translateWitnessInvariant(loc, invariants, x -> x.isAt(), node);
				if (list.isEmpty()) {
					result = null;
				} else {
					assert list.size() == 1;
					result = list.get(0);
				}
			} catch (final IncorrectSyntaxException ise) {
				mLogger.error("The following invariant contains an incorrect syntax and was ignored. Reason: "
						+ ise.getMessage());
				mLogger.error(invariants);
				result = null;
			} catch (final UnsupportedSyntaxException use) {
				mLogger.warn("The following invariant contains an usupported syntax and was ignored. Reason: "
						+ use.getMessage());
				mLogger.warn(invariants);
				result = null;
			}
		}
		return result;
	}

	private void handleWitnessInvariantsBeforeDispatch(final IASTNode n) throws AssertionError {
		if (mWitnessInvariants == null) {
			return;
		}
		final ExtractedWitnessInvariant rawWitnessInvariant = mWitnessInvariants.get(n);
		final ILocation loc = mLocationFactory.createCLocation(n);
		final List<AssertStatement> translatedWitnessInvariant =
				translateWitnessInvariant(loc, rawWitnessInvariant, a -> a.isBefore(), n);
		mCurrentWitnessInvariants.push(new WitnessInvariant(translatedWitnessInvariant, rawWitnessInvariant));
	}

	private void handleWitnessInvariantsAfterDispatch(final IASTNode node, final Result result) throws AssertionError {
		if (mWitnessInvariants == null) {
			assert mCurrentWitnessInvariants.isEmpty();
			return;
		}

		final WitnessInvariant before = mCurrentWitnessInvariants.pop();
		final List<AssertStatement> translatedWitnessInvariant = before.getTranslatedWitnessInvariant();
		final ExtractedWitnessInvariant rawWitnessInvariant = before.getRawWitnessInvariant();

		// TODO: Use the new information as you see fit
		final ExtractedWitnessInvariant afterWitnessInvariantRaw = mWitnessInvariants.get(node);
		final List<AssertStatement> afterTranslatedWitnessInvariants = translateWitnessInvariant(
				mLocationFactory.createCLocation(node), afterWitnessInvariantRaw, a -> a.isAfter(), node);

		if (translatedWitnessInvariant.isEmpty() && afterTranslatedWitnessInvariants.isEmpty()) {
			return;
		}

		final ILocation loc = mLocationFactory.createCLocation(node);
		if (result instanceof ExpressionResult) {
			final ExpressionResult exprResult = (ExpressionResult) result;
			final List<Statement> stmt = exprResult.getStatements();
			if (rawWitnessInvariant != null
					&& !mNodeLabelsOfAddedWitnesses.contains(rawWitnessInvariant.getNodeLabels())) {
				stmt.addAll(0, translatedWitnessInvariant);
				mNodeLabelsOfAddedWitnesses.add(rawWitnessInvariant.getNodeLabels());
				mLogger.info("Checking witness invariant " + rawWitnessInvariant
						+ " directly before the following code " + loc);
			}
			if (afterWitnessInvariantRaw != null
					&& !mNodeLabelsOfAddedWitnesses.contains(afterWitnessInvariantRaw.getNodeLabels())) {
				stmt.addAll(afterTranslatedWitnessInvariants);
				mNodeLabelsOfAddedWitnesses.add(afterWitnessInvariantRaw.getNodeLabels());
				mLogger.info("Checking witness invariant " + afterWitnessInvariantRaw
						+ " directly after the following code " + loc);
			}
		} else if (result instanceof ExpressionListResult) {
			final ExpressionListResult exlire = (ExpressionListResult) result;
			if (rawWitnessInvariant != null
					&& !mNodeLabelsOfAddedWitnesses.contains(rawWitnessInvariant.getNodeLabels())) {
				final List<Statement> stmt = exlire.getList().get(0).getStatements();
				stmt.addAll(0, translatedWitnessInvariant);
				mNodeLabelsOfAddedWitnesses.add(rawWitnessInvariant.getNodeLabels());
				mLogger.warn("Checking witness invariant " + rawWitnessInvariant
						+ " directly before the following code " + loc);
			}
			if (afterWitnessInvariantRaw != null
					&& !mNodeLabelsOfAddedWitnesses.contains(afterWitnessInvariantRaw.getNodeLabels())) {
				final List<Statement> stmt = exlire.getLast().getStatements();
				stmt.addAll(afterTranslatedWitnessInvariants);
				mNodeLabelsOfAddedWitnesses.add(afterWitnessInvariantRaw.getNodeLabels());
				mLogger.warn("Checking witness invariant " + afterWitnessInvariantRaw
						+ " directly after the following code " + loc);
			}
		} else {
			if (rawWitnessInvariant != null
					&& !mNodeLabelsOfAddedWitnesses.contains(rawWitnessInvariant.getNodeLabels())) {
				final String message = "Found witness invariant but unable to add check " + rawWitnessInvariant
						+ " directly before the following code " + loc;
				mLogger.warn(message);
			}
			if (afterWitnessInvariantRaw != null
					&& !mNodeLabelsOfAddedWitnesses.contains(afterWitnessInvariantRaw.getNodeLabels())) {
				final String message = "Found witness invariant but unable to add check " + afterWitnessInvariantRaw
						+ " directly after the following code " + loc;
				mLogger.warn(message);
			}
		}
	}

	private List<AssertStatement> translateWitnessInvariant(final ILocation loc,
			final ExtractedWitnessInvariant invariant,
			final java.util.function.Predicate<ExtractedWitnessInvariant> funHasCorrectPosition, final IASTNode hook)
			throws AssertionError {
		if (invariant != null) {
			if (!funHasCorrectPosition.test(invariant)) {
				return Collections.emptyList();
			}
			ACSLNode acslNode = null;
			try {
				checkForQuantifiers(invariant.getInvariant());
				acslNode = Parser.parseComment("lstart\n assert " + invariant.getInvariant() + ";",
						invariant.getStartline(), 1, mLogger);
			} catch (final ACSLSyntaxErrorException e) {
				throw new UnsupportedSyntaxException(loc, e.getMessage());
			} catch (final Exception e) {
				throw new AssertionError(e);
			}
			final Result translationResult = dispatch(acslNode, hook);
			final List<AssertStatement> invariants = new ArrayList<>();
			if (translationResult instanceof ExpressionResult) {
				final ExpressionResult exprResult = (ExpressionResult) translationResult;
				if (!exprResult.getAuxVars().isEmpty()) {
					throw new UnsupportedSyntaxException(loc,
							"must be translatable without auxvars " + exprResult.getAuxVars().toString());
				}
				if (!exprResult.getDeclarations().isEmpty()) {
					throw new UnsupportedSyntaxException(loc,
							"must be translatable without new declarations" + exprResult.getDeclarations().toString());
				}
				if (!exprResult.getOverapprs().isEmpty()) {
					throw new UnsupportedSyntaxException(loc, "must be translatable without new overapproximations"
							+ exprResult.getOverapprs().toString());
				}
				if (exprResult.getStatements().size() > 1) {
					throw new UnsupportedSyntaxException(loc, "must be translatable without additional statements"
							+ exprResult.getStatements().toString());
				}
				final Statement stmt = exprResult.getStatements().get(0);
				if (stmt instanceof AssertStatement) {
					invariants.add((AssertStatement) stmt);
				} else {
					throw new AssertionError("must return one AssertStatement");
				}
			}
			return invariants;
		}
		return Collections.emptyList();
	}

	/**
	 * Throw Exception if invariant contains quantifiers. It seems like our parser does not support quantifiers yet, For
	 * the moment it seems to be better to crash here in order to get a meaningful error message.
	 */
	private static void checkForQuantifiers(final String invariant) {
		if (invariant.contains("exists") || invariant.contains("forall")) {
			throw new UnsupportedSyntaxException(LocationFactory.createIgnoreCLocation(),
					"invariant contains quantifiers");
		}

	}

	private static final class WitnessInvariant {
		private final List<AssertStatement> mTranslatedWitnessInvariant;
		private final ExtractedWitnessInvariant mRawWitnessInvariant;

		public WitnessInvariant(final List<AssertStatement> translatedWitnessInvariant,
				final ExtractedWitnessInvariant rawWitnessInvariant) {
			mTranslatedWitnessInvariant = translatedWitnessInvariant;
			mRawWitnessInvariant = rawWitnessInvariant;
		}

		public List<AssertStatement> getTranslatedWitnessInvariant() {
			return mTranslatedWitnessInvariant;
		}

		public ExtractedWitnessInvariant getRawWitnessInvariant() {
			return mRawWitnessInvariant;
		}

	}
}
