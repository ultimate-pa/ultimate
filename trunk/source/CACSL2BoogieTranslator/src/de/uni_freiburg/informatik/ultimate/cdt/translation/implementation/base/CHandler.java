/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
/**
 * The base C handler implementation.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.text.ParseException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import org.eclipse.cdt.core.dom.ast.IASTASMDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTArrayDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTArrayModifier;
import org.eclipse.cdt.core.dom.ast.IASTArraySubscriptExpression;
import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTBreakStatement;
import org.eclipse.cdt.core.dom.ast.IASTCaseStatement;
import org.eclipse.cdt.core.dom.ast.IASTCastExpression;
import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
import org.eclipse.cdt.core.dom.ast.IASTConditionalExpression;
import org.eclipse.cdt.core.dom.ast.IASTContinueStatement;
import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;
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
import org.eclipse.cdt.core.dom.ast.IASTFunctionDeclarator;
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
import org.eclipse.cdt.core.dom.ast.IASTPointerOperator;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorStatement;
import org.eclipse.cdt.core.dom.ast.IASTProblem;
import org.eclipse.cdt.core.dom.ast.IASTProblemDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTProblemExpression;
import org.eclipse.cdt.core.dom.ast.IASTProblemStatement;
import org.eclipse.cdt.core.dom.ast.IASTProblemTypeId;
import org.eclipse.cdt.core.dom.ast.IASTReturnStatement;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTStandardFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IASTSwitchStatement;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.IASTTypeIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTWhileStatement;
import org.eclipse.cdt.core.dom.ast.c.ICASTCompositeTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.gnu.IGNUASTCompoundStatementExpression;
import org.eclipse.cdt.core.dom.ast.gnu.c.ICASTKnRFunctionDeclarator;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTDesignatedInitializer;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTFunctionDeclarator;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTLiteralExpression;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.annotation.LTLPropertyCheck;
import de.uni_freiburg.informatik.ultimate.boogie.annotation.LTLPropertyCheck.CheckableExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BreakStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.decorator.DecoratedUnit;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ArrayHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.BoogieTypeHelper;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.FunctionHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.InitializationHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.LocalLValueILocationPair;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.PostProcessor;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ProcedureManager;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.StaticObjectsHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.StructHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.BitvectorTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.IntegerTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitiveCategory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CUnion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CStorageClass;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ContractResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.DeclarationResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.DeclaratorResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionListResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.InitializerResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.InitializerResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValueFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValueForArrays;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.SkipResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.StringLiteralResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.TypesResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ICHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CodeAnnot;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Contract;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.GlobalLTLInvariant;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.CACSL2BoogieBacktranslator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.LTLExpressionExtractor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.PointerCheckMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.PointerIntegerConversion;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.UnsignedTreatment;

/**
 * Class that handles translation of C nodes to Boogie nodes.
 *
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @author Matthias Heizmann
 * @author Alexander Nutz
 */
public class CHandler implements ICHandler {

	/**
	 * If set to true we say Unsupported Syntax if there is some cast of pointers. Right now we are unable to handle
	 * casts of pointers soundly. However these soundness errors occur seldom.
	 */
	private static final boolean POINTER_CAST_IS_UNSUPPORTED_SYNTAX = false;

	private static int computeSizeOfInitializer(final IASTEqualsInitializer equalsInitializer) {
		final int intSizeFactor;
		// assert equalsInitializer.getInitializerClause() instanceof
		// IASTInitializerList;

		if (equalsInitializer.getInitializerClause() instanceof IASTInitializerList) {
			final IASTInitializerList initList = (IASTInitializerList) equalsInitializer.getInitializerClause();
			intSizeFactor = initList.getSize();
			return intSizeFactor;
		} else if (equalsInitializer.getInitializerClause() instanceof CASTLiteralExpression
				&& ((CASTLiteralExpression) equalsInitializer.getInitializerClause())
						.getKind() == IASTLiteralExpression.lk_string_literal) {
			final CASTLiteralExpression lit = (CASTLiteralExpression) equalsInitializer.getInitializerClause();
			/*
			 * subtracting -1 because lit.getValue includes the quotation marks (-2) and we will add a termination
			 * character (+1), for example the string literals "bla" will give us length 7, as C will store it as 'b'
			 * 'l' 'a' '\0'
			 */
			return lit.getValue().length - 1;
		} else {
			throw new AssertionError("attempting to compute size of an unforseen kind of initializer expression");
		}
	}

	private static void convertPointerToPointer(final ILocation loc, final ExpressionResult rexp,
			final CPointer newType) {
		// TODO: check if types are compatible
		assert rexp.mLrVal instanceof RValue : "has to be converted to RValue";
		final RValue oldRvalue = (RValue) rexp.mLrVal;
		assert oldRvalue.getCType() instanceof CPointer : "has to be pointer";
		final RValue newRvalue = new RValue(oldRvalue.getValue(), newType);
		rexp.mLrVal = newRvalue;
	}

	private static void convertToVoid(final ILocation loc, final ExpressionResult rexp, final CPrimitive newType) {
		assert rexp.mLrVal instanceof RValue : "has to be converted to RValue";
		final CType oldType = rexp.mLrVal.getCType().getUnderlyingType();
		if (oldType instanceof CPrimitive) {
			// ok
		} else if (oldType instanceof CPointer) {
			// ok
		} else if (oldType instanceof CEnum) {
			// ok
		} else if (oldType instanceof CArray) {
			throw new AssertionError("cannot convert from CArray");
		} else if (oldType instanceof CFunction) {
			throw new AssertionError("cannot convert from CFunction");
		} else if (oldType instanceof CStruct) {
			if (newType.getType() == CPrimitives.VOID) {
				// ok: we just keep the old value but change the type
				// alternative might be to set the value to null because it should never be used
			} else {
				throw new UnsupportedSyntaxException(loc, "cannot convert from CStruct to " + newType);
			}
		} else {
			throw new AssertionError("unknown type " + newType);
		}
		final RValue oldRValue = (RValue) rexp.mLrVal;
		final RValue resultRvalue =
				new RValue(oldRValue.getValue(), newType, oldRValue.isBoogieBool(), oldRValue.isIntFromPointer());
		rexp.mLrVal = resultRvalue;
	}

	private static LoopInvariantSpecification fetchWitnessInvariantAtLoop(final Dispatcher main,
			final IASTStatement node) {
		final LoopInvariantSpecification witnessInvariant;
		if (main instanceof MainDispatcher) {
			witnessInvariant = ((MainDispatcher) main).fetchInvariantAtLoop(node);
		} else {
			witnessInvariant = null;
		}
		return witnessInvariant;
	}

	/**
	 * Handle the address operator according to Section 6.5.3.2 of C11.
	 */
	private static Result handleAddressOfOperator(final Dispatcher main, final ExpressionResult er, final ILocation loc,
			final IASTNode hook) throws AssertionError {
		final RValue ad;
		if (er.mLrVal instanceof HeapLValue) {
			ad = ((HeapLValue) er.getLrValue()).getAddressAsPointerRValue(main.mTypeHandler.getBoogiePointerType());
			// new RValue(((HeapLValue) er.mLrVal).getAddress(), new
			// CPointer(er.mLrVal.getCType()));
		} else if (er.mLrVal instanceof LocalLValue) {
			if (main instanceof PRDispatcher) {
				// We are in the prerun mode.
				// As a workaround, we (incorrectly) return the value
				// instead of the address. But we add variables to the
				// heapVars and hence in the non-prerun mode the input
				// will be a HeapLValue instead of a LocalLValue.
				final Expression expr = er.mLrVal.getValue();
				if (expr instanceof IdentifierExpression) {
					final IdentifierExpression idExpr = (IdentifierExpression) expr;
					((PRDispatcher) main).moveIdOnHeap(loc, idExpr, hook);
				} else {
					((PRDispatcher) main).moveArrayAndStructIdsOnHeap(loc, expr, er.mAuxVars, hook);
				}
				ad = convertToPointerRValue(main, er.getLrValue(), main.mTypeHandler.getBoogiePointerType());
				// ad = new RValue(expr, new CPointer(er.mLrVal.getCType()));
				// ad = new RValue(ExpressionFactory.modifyExpression(expr,
				// x -> x,
				// x ->main.mTypeHandler.getBoogiePointerType()),
				// new CPointer(er.mLrVal.getCType()));
			} else {
				throw new AssertionError("cannot take address of LocalLValue: this is a on-heap/off-heap bug");
			}
		} else if (er.mLrVal instanceof RValue) {
			throw new AssertionError("cannot take address of RValue");
		} else {
			throw new AssertionError("Unknown value");
		}
		final ExpressionResult result = ExpressionResult.copyStmtDeclAuxvarOverapprox(er);
		result.mLrVal = ad;
		return result;
	}

	private static RValue convertToPointerRValue(final Dispatcher main, final LRValue lrValue,
			final BoogieType pointerType) {
		assert main.mCHandler.isPreRunMode();
		if (lrValue instanceof HeapLValue) {
			throw new AssertionError("does this occur??");
		}
		final Expression oldValue = lrValue.getValue();
		final Expression convertedValue = ExpressionFactory.replaceBoogieType(oldValue, pointerType);

		return new RValue(convertedValue, new CPointer(lrValue.getCType()));
	}

	/**
	 * Whether or not a new Scope should be started for this compound statement.
	 *
	 * @param env
	 *            the environment in which the CompoundStatement is.
	 * @return whether to open a new scope in the symbol table or not.
	 */
	private static boolean isNewScopeRequired(final IASTNode env) {
		return !(env instanceof IASTForStatement) && !(env instanceof IASTFunctionDefinition);
	}

	private final MemoryHandler mMemoryHandler;

	private final ArrayHandler mArrayHandler;

	private final StaticObjectsHandler mStaticObjectsHandler;

	private final FunctionHandler mFunctionHandler;

	private final PostProcessor mPostProcessor;

	private final INameHandler mNameHandler;

	private final InitializationHandler mInitHandler;
	private final LinkedHashSet<String> mBoogieIdsOfHeapVars;

	/**
	 * Stores the labels of the loops we are currently inside. (For translation of a possible continue statement)
	 */
	private final Deque<String> mInnerMostLoopLabel;

	private final ILogger mLogger;

	private final CACSLPreferenceInitializer.UnsignedTreatment mUnsignedTreatment;

	private final List<LTLExpressionExtractor> mGlobAcslExtractors;
	private final StandardFunctionHandler mStandardFunctionHandler;

	protected final ITypeHandler mTypeHandler;

	protected final StructHandler mStructHandler;

	/**
	 * Contract for next procedure
	 */
	protected final List<ACSLNode> mContract;

	/**
	 * The symbol table for the translation.
	 */
	protected final FlatSymbolTable mSymbolTable;

	/**
	 * A set holding declarations of global variables required for variables, declared locally in C but required to be
	 * global in Boogie. e.g. constants for enums (in boogie constants may only be defined globally) or local static
	 * variables. Each declaration can have a set of initialization statements. So the procedure is: typeDeclarations:
	 * added to this map in IASTSimpleDeclaration, declared using this map in ITranslationUnit static variables: added
	 * to this map in IASTSimpleDeclaration, declared using this map in ITranslationUnit, initialized using this map in
	 * PostProcessor.createInit..() global variables: added to this map in IASTTranslationUnit, declared using this map
	 * in ITranslationUnit, initialized using this map in PostProcessor.createInit..()
	 */
	// protected final LinkedHashMap<Declaration, CDeclaration>
	// mDeclarationsGlobalInBoogie;

	/**
	 * A collection of axioms generated during translation process.
	 */
	protected final LinkedHashSet<Axiom> mAxioms;

	/**
	 * Translation from Boogie to C for traces and expressions.
	 */
	protected final CACSL2BoogieBacktranslator mBacktranslator;

	/**
	 * If set to true and the program contains an error label ULTIMATE shows a warning that suggests a different
	 * translation mode.
	 */
	protected final boolean mErrorLabelWarning;

	protected final ExpressionTranslation mExpressionTranslation;

	protected final TypeSizeAndOffsetComputer mTypeSizeComputer;

	/**
	 * Holds the next ACSL node in the decorator tree.
	 */
	private NextACSL mAcsl;

	/**
	 * This is a stack containing the types of the things declared IASTDeclarator nodes. The last element on the stack
	 * corresponds to the type of the current (inner) declarator node. There may be several types on this stack if the
	 * declarators are nested, as in
	 *
	 * <pre>
	 * int *(*a(int))[3]
	 * </pre>
	 *
	 * which declares a function returning a pointer to an array of length three containing int pointers. There are
	 * three nested declarators: A PointerDeclarator contains an ArrayDeclarator contains a Pointer contains a function.
	 */
	protected ArrayDeque<TypesResult> mCurrentDeclaredTypes;

	private final BoogieTypeHelper mBoogieTypeHelper;

	private final Dispatcher mMainDispatcher;

	private final ProcedureManager mProcedureManager;

	private final HandlerHandler mHandlerHandler;

	/**
	 * The boogie declarations that are the result of the translation process.
	 */
	private final ArrayList<Declaration> mDeclarations;

	/**
	 * Constructor.
	 *
	 * @param main
	 *            a reference to the main dispatcher.
	 * @param backtranslator
	 *            a reference to the Backtranslator object.
	 * @param overapproximateFloatingPointOperations
	 * @param nameHandler
	 * @param mst
	 *            the symbol table which contains the information about which file uses which declaration
	 */
	public CHandler(final Dispatcher main, final HandlerHandler handlerHandler,
			final CACSL2BoogieBacktranslator backtranslator, final boolean errorLabelWarning, final ILogger logger, // final
																													// ITypeHandler
																													// typeHandler,
			final boolean bitvectorTranslation, final boolean overapproximateFloatingPointOperations,
			final FlatSymbolTable ftab) {
		final IPreferenceProvider prefs = main.getPreferences();

		mHandlerHandler = handlerHandler;
		mHandlerHandler.setCHandler(this);

		mMainDispatcher = main;

		mLogger = logger;
		mTypeHandler = handlerHandler.getTypeHandler();
		mTypeHandler.setCHandler(this);
		mNameHandler = handlerHandler.getNameHandler();
		mBacktranslator = backtranslator;
		mErrorLabelWarning = errorLabelWarning;

		mUnsignedTreatment = prefs.getEnum(CACSLPreferenceInitializer.LABEL_UNSIGNED_TREATMENT,
				CACSLPreferenceInitializer.UnsignedTreatment.class);

		mArrayHandler = new ArrayHandler(prefs);
		mStaticObjectsHandler = new StaticObjectsHandler();

		mSymbolTable = ftab;

		// mDeclarationsGlobalInBoogie = new LinkedHashMap<>();
		mAxioms = new LinkedHashSet<>();
		mContract = new ArrayList<>();
		mInnerMostLoopLabel = new ArrayDeque<>();
		mBoogieIdsOfHeapVars = new LinkedHashSet<>();
		mCurrentDeclaredTypes = new ArrayDeque<>();
		mGlobAcslExtractors = new ArrayList<>();

		final PointerIntegerConversion pointerIntegerConversion =
				prefs.getEnum(CACSLPreferenceInitializer.LABEL_POINTER_INTEGER_CONVERSION,
						CACSLPreferenceInitializer.PointerIntegerConversion.class);
		if (bitvectorTranslation) {
			mExpressionTranslation = new BitvectorTranslation(main.getTypeSizes(), handlerHandler,
					pointerIntegerConversion, overapproximateFloatingPointOperations);
		} else {
			final boolean inRange = prefs.getBoolean(CACSLPreferenceInitializer.LABEL_ASSUME_NONDET_VALUES_IN_RANGE);
			mExpressionTranslation = new IntegerTranslation(main.getTypeSizes(), handlerHandler, mUnsignedTreatment,
					inRange, pointerIntegerConversion, overapproximateFloatingPointOperations);
		}

		mTypeHandler.setExpressionTranslation(mExpressionTranslation);
		mBoogieTypeHelper = new BoogieTypeHelper(handlerHandler);

		mPostProcessor =
				new PostProcessor(main, mLogger, mExpressionTranslation, overapproximateFloatingPointOperations);
		mTypeSizeComputer = new TypeSizeAndOffsetComputer(handlerHandler, main.getTypeSizes());

		mProcedureManager = new ProcedureManager(handlerHandler);
		mFunctionHandler = new FunctionHandler(handlerHandler);

		final boolean smtBoolArraysWorkaround =
				prefs.getBoolean(CACSLPreferenceInitializer.LABEL_SMT_BOOL_ARRAYS_WORKAROUND);
		final boolean checkPointerValidity = prefs.getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_POINTER_VALIDITY);
		mMemoryHandler = new MemoryHandler(mHandlerHandler, checkPointerValidity, main.getTypeSizes(),
				bitvectorTranslation, handlerHandler.getNameHandler(), smtBoolArraysWorkaround, prefs);
		mStructHandler = new StructHandler(handlerHandler);
		mInitHandler = new InitializationHandler(mMemoryHandler, mExpressionTranslation, mProcedureManager);

		mStandardFunctionHandler = new StandardFunctionHandler(mTypeHandler, mExpressionTranslation, mMemoryHandler,
				mStructHandler, mTypeSizeComputer, mFunctionHandler, mProcedureManager, this);

		mDeclarations = new ArrayList<>();
	}

	/**
	 * @deprecated is not supported in this handler! Do not use!
	 */
	@Deprecated
	@Override
	public Result visit(final Dispatcher main, final ACSLNode node) {
		throw new UnsupportedOperationException("Implementation Error: Use ACSLHandler for: " + node.getClass());
	}

	@Override
	public Result visit(final Dispatcher main, final CASTDesignatedInitializer node) {
		return mStructHandler.handleDesignatedInitializer(main, mMemoryHandler, mStructHandler, node);
	}

	@Override
	public Result visit(final Dispatcher main, final List<DecoratedUnit> units) {
		IASTNode globalHook = null;
		for (final DecoratedUnit du : units) {
			if (du.getRootNode().getCNode() != null) {
				if (main instanceof MainDispatcher) {
					((MainDispatcher) main).updateDecoratorTreeAndIterator(du.getRootNode());
				}
				visit(main, (IASTTranslationUnit) du.getRootNode().getCNode());
				globalHook = du.getRootNode().getCNode();
			}
			// ACSL?
		}

		// Generate additional boogie translation that is collected for all files.
		final ILocation loc = LocationFactory.createIgnoreCLocation();

		// (alex:) new function pointers
		final BigInteger functionPointerPointerBaseValue = BigInteger.valueOf(-1);
		for (final Entry<String, Integer> en : main.getFunctionToIndex().entrySet()) {
			final String funcId = SFO.FUNCTION_ADDRESS + en.getKey();
			final VarList varList = new VarList(loc, new String[] { funcId }, mTypeHandler.constructPointerType(loc));
			// would unique make sense here?? -- would potentially add lots of axioms
			mDeclarations.add(new ConstDeclaration(loc, new Attribute[0], false, varList, null, false));

			final Expression funcIdExpr = ExpressionFactory.constructIdentifierExpression(loc,
					mBoogieTypeHelper.getBoogieTypeForPointerType(), funcId,
					DeclarationInformation.DECLARATIONINFO_GLOBAL);

			final BigInteger offsetValue = BigInteger.valueOf(en.getValue());
			mDeclarations.add(new Axiom(loc, new Attribute[0],
					ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, funcIdExpr,
							mExpressionTranslation.constructPointerForIntegerValues(loc,
									functionPointerPointerBaseValue, offsetValue))));
		}

		mDeclarations.addAll(mAxioms);

		mDeclarations.addAll(0, mPostProcessor.postProcess(main, loc, globalHook));

		/*
		 * this must come after the post processor because the post processor might add declarations when dispatching
		 * initializers of static variables
		 */
		mDeclarations.addAll(getStaticObjectsHandler().getGlobalDeclarations());

		// this has to happen after postprocessing as pping may add sizeof
		// constants for initializations
		mDeclarations.addAll(mTypeSizeComputer.getConstants());
		mDeclarations.addAll(mTypeSizeComputer.getAxioms());
		mDeclarations.addAll(mMemoryHandler.declareMemoryModelInfrastructure(main, loc, globalHook));
		mDeclarations.addAll(mInitHandler.declareInitializationInfrastructure(main, loc));

		// add type declarations introduced by the translation, e.g., $Pointer$
		mDeclarations.addAll(
				((TypeHandler) mTypeHandler).constructTranslationDefiniedDelarations(loc, mExpressionTranslation));

		/**
		 * For Notes on our handling of procedures see {@link FunctionHandler.handleFunctionDefinition(..)}. Short
		 * version:
		 * <li>procedure implementations have already been inserted into the Boogie program by code above
		 * <li>procedure declarations have been collected in the FunctionHandler
		 * <li>now we recompute the declarations, in order to give them correct modifies clauses and insert them into
		 * the Boogie program
		 *
		 * have to block this in prerun, because there, memory model is not declared which may cause problems with the
		 * call graph computation
		 */
		if (!(main instanceof PRDispatcher)) {
			// handle proc. declaration & resolve their transitive modified globals
			mDeclarations.addAll(mProcedureManager.computeFinalProcedureDeclarations(main, mMemoryHandler));
		}

		/**
		 * Add declarations of Boogie functions (as opposed to Boogie procedures) to the Boogie program that have been
		 * collected by the ExpressionTranslation
		 */
		final Collection<FunctionDeclaration> declaredFunctions =
				mExpressionTranslation.getFunctionDeclarations().getDeclaredFunctions().values();
		mDeclarations.addAll(declaredFunctions);

		// TODO Need to get a CLocation from somewhere
		// the overall translation result:
		final Unit boogieUnit = new Unit(
				main.getLocationFactory().createRootCLocation(
						units.stream().map(a -> a.getSourceTranslationUnit()).collect(Collectors.toSet())),
				mDeclarations.toArray(new Declaration[mDeclarations.size()]));
		final IASTTranslationUnit hook = units.stream().findAny().get().getSourceTranslationUnit();

		// annotate the Unit with LTLPropertyChecks if applicable
		for (final LTLExpressionExtractor ex : mGlobAcslExtractors) {
			final Map<String, LTLPropertyCheck.CheckableExpression> checkableAtomicPropositions = new LinkedHashMap<>();

			for (final Entry<String, de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression> en : ex
					.getAP2SubExpressionMap().entrySet()) {
				final ExpressionResult r = (ExpressionResult) main.dispatch(en.getValue(), hook);
				// TODO: some switchToRValue and handling of sideeffects?
				checkableAtomicPropositions.put(en.getKey(), new CheckableExpression(r.mLrVal.getValue(), null));
			}
			final LTLPropertyCheck propCheck =
					new LTLPropertyCheck(ex.getLTLFormatString(), checkableAtomicPropositions, null);
			propCheck.annotate(boogieUnit);
		}

		return new Result(boogieUnit);
	}

	@Override
	public Result visit(final Dispatcher main, final IASTArraySubscriptExpression node) {
		return mArrayHandler.handleArraySubscriptExpression(main, mMemoryHandler, mStructHandler, node);
	}

	@Override
	public Result visit(final Dispatcher main, final IASTASMDeclaration node) {
		if (main.isSvcomp()) {
			// workaround for now: ignore inline assembler instructions
			return new SkipResult();
		}
		final String msg = "CHandler: Not yet implemented: \"" + node.getRawSignature() + "\" (Type: "
				+ node.getClass().getName() + ")";
		throw new UnsupportedSyntaxException(main.getLocationFactory().createCLocation(node), msg);
	}

	@Override
	public Result visit(final Dispatcher main, final IASTBinaryExpression node) {
		// final ArrayList<Declaration> decl = new ArrayList<>();
		// final ArrayList<Statement> stmt = new ArrayList<>();
		// final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		// final List<Overapprox> overappr = new ArrayList<>();

		final ExpressionResult leftOperand = (ExpressionResult) main.dispatch(node.getOperand1());
		final ExpressionResult rightOperand = (ExpressionResult) main.dispatch(node.getOperand2());

		// final ExpressionResult rl = leftOperand.switchToRValueIfNecessary(main, loc);
		// final ExpressionResult rr = rightOperand.switchToRValueIfNecessary(main,
		// loc);

		// final CType lType = leftOperand.mLrVal.getCType().getUnderlyingType();
		// final CType rType = rightOperand.mLrVal.getCType().getUnderlyingType();

		switch (node.getOperator()) {
		case IASTBinaryExpression.op_assign: {
			// stmt.addAll(leftOperand.mStmt);
			// decl.addAll(leftOperand.mDecl);
			// auxVars.putAll(leftOperand.mAuxVars);
			// overappr.addAll(leftOperand.mOverappr);
			final ExpressionResultBuilder builder = new ExpressionResultBuilder();
			builder.addAllExceptLrValue(leftOperand);

			final CType lType = leftOperand.mLrVal.getCType().getUnderlyingType();
			final CType rType = rightOperand.mLrVal.getCType().getUnderlyingType();

			if (lType instanceof CPointer && rType instanceof CArray) {
				/*
				 * assigning an array to a pointer the array must be on heap --> just take the address
				 */

				// stmt.addAll(rightOperand.mStmt);
				// decl.addAll(rightOperand.mDecl);
				// auxVars.putAll(rightOperand.mAuxVars);
				// overappr.addAll(rightOperand.mOverappr);
				builder.addAllExceptLrValue(rightOperand);

				final LRValue rightLrVal = rightOperand.mLrVal;

				final RValue address = decayArrayLrValToPointer(loc, rightLrVal, node);
				builder.setLrVal(address);
				// return makeAssignment(main, loc, stmt, leftOperand.mLrVal, address, decl,
				// auxVars, overappr);
				return makeAssignment(main, loc, leftOperand.mLrVal, Collections.emptyList(), builder.build(), node);
			}

			final ExpressionResult rightOperandSwitched = rightOperand.switchToRValueIfNecessary(main, loc, node);
			// rr.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			rightOperandSwitched.rexBoolToIntIfNecessary(loc, mExpressionTranslation);

			// stmt.addAll(rr.mStmt);
			// decl.addAll(rr.mDecl);
			// auxVars.putAll(rr.mAuxVars);
			// overappr.addAll(rr.mOverappr);
			builder.addAllExceptLrValue(rightOperandSwitched);

			builder.setLrVal(rightOperandSwitched.getLrValue());

			return makeAssignment(main, loc, leftOperand.mLrVal, // (RValue) rr.mLrVal, decl, auxVars, overappr,
					leftOperand.mOtherUnionFields, builder.build(), node);
			// return makeAssignment(main, loc, stmt, leftOperand.mLrVal, (RValue)
			// rr.mLrVal, decl, auxVars, overappr,
			// leftOperand.mOtherUnionFields);

		}
		case IASTBinaryExpression.op_equals:
		case IASTBinaryExpression.op_notequals: {
			final ExpressionResult rl = leftOperand.switchToRValueIfNecessary(main, loc, node);
			final ExpressionResult rr = rightOperand.switchToRValueIfNecessary(main, loc, node);
			rr.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			rl.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			return handleEqualityOperators(main, loc, node.getOperator(), rl, rr);
		}
		case IASTBinaryExpression.op_greaterEqual:
		case IASTBinaryExpression.op_greaterThan:
		case IASTBinaryExpression.op_lessEqual:
		case IASTBinaryExpression.op_lessThan: {
			final ExpressionResult rl = leftOperand.switchToRValueIfNecessary(main, loc, node);
			final ExpressionResult rr = rightOperand.switchToRValueIfNecessary(main, loc, node);
			return handleRelationalOperators(main, loc, node.getOperator(), rl, rr);
		}

		case IASTBinaryExpression.op_logicalAnd: {
			final ExpressionResult rl = leftOperand.switchToRValueIfNecessary(main, loc, node);
			final ExpressionResult rr = rightOperand.switchToRValueIfNecessary(main, loc, node);
			rl.rexIntToBoolIfNecessary(loc, mExpressionTranslation, mMemoryHandler);
			rr.rexIntToBoolIfNecessary(loc, mExpressionTranslation, mMemoryHandler);

			final ExpressionResultBuilder builder = new ExpressionResultBuilder();
			// stmt.addAll(rl.mStmt);
			// // NOTE: no rr.stmt
			// decl.addAll(rl.mDecl);
			// decl.addAll(rr.mDecl);
			// auxVars.putAll(rl.mAuxVars);
			// auxVars.putAll(rr.mAuxVars);
			// overappr.addAll(rl.mOverappr);
			// overappr.addAll(rr.mOverappr);
			builder.addAllExceptLrValue(rl);
			// NOTE: do not unconditionally add rr.stmt as it may be short-circuited
			builder.addDeclarations(rr.getDeclarations());
			// builder.putAuxVars(rr.getAuxVars());
			builder.addAuxVars(rr.getAuxVars());
			builder.addOverapprox(rr.getOverapprs());

			if (rr.mStmt.isEmpty()) {
				// no statements in right operands, hence no side effects in
				// operand
				// we can directly combine operands with LOGICAND
				final RValue newRVal = new RValue(
						ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND,
								rl.mLrVal.getValue(), rr.mLrVal.getValue()),
						new CPrimitive(CPrimitive.CPrimitives.INT), true);

				builder.setLrVal(newRVal);
				return builder.build();
				// return new ExpressionResult(stmt, newRVal, decl, auxVars, overappr);
			}
			// create and add tmp var #t~AND~UID
			final CPrimitive intType = new CPrimitive(CPrimitives.INT);
			// final String resName = mNameHandler.getTempVarUID(SFO.AUXVAR.SHORTCIRCUIT,
			// intType);
			// final VarList tempVar = new VarList(loc, new String[] { resName }, new
			// PrimitiveType(loc, SFO.BOOL));
			// final VariableDeclaration tmpVar =
			// new VariableDeclaration(loc, new Attribute[0], new VarList[] { tempVar });
			final AuxVarInfo resNameAuxvar = AuxVarInfo.constructAuxVarInfo(loc, main, intType,
					new PrimitiveType(loc, BoogieType.TYPE_BOOL, SFO.BOOL), SFO.AUXVAR.SHORTCIRCUIT);
			// auxVars.put(tmpVar, loc);
			// decl.add(tmpVar);
			builder.addDeclaration(resNameAuxvar.getVarDec());
			// builder.putAuxVar(resNameAuxvar.getVarDec(), loc);
			builder.addAuxVar(resNameAuxvar);
			// final VariableLHS lhs = new VariableLHS(loc, resName);
			final RValue tmpRval = new RValue(resNameAuxvar.getExp(), intType, true);
			final RValue resRval = tmpRval;
			// #t~AND~UID = left

			final AssignmentStatement aStat = StatementFactory.constructAssignmentStatement(loc,
					new LeftHandSide[] { resNameAuxvar.getLhs() }, new Expression[] { rl.mLrVal.getValue() });
			// for (final Overapprox overapprItem : overappr) {
			for (final Overapprox overapprItem : builder.getOverappr()) {
				overapprItem.annotate(aStat);
			}
			// stmt.add(aStat);
			builder.addStatement(aStat);
			// if (#t~AND~UID) {#t~AND~UID = right;}
			final ArrayList<Statement> outerThenPart = new ArrayList<>();
			outerThenPart.addAll(rr.mStmt);

			outerThenPart.add(StatementFactory.constructAssignmentStatement(loc,
					new LeftHandSide[] { resNameAuxvar.getLhs() }, new Expression[] { rr.mLrVal.getValue() }));
			final IfStatement ifStatement = new IfStatement(loc, tmpRval.getValue(),
					outerThenPart.toArray(new Statement[outerThenPart.size()]), new Statement[0]);
			// stmt.add(ifStatement);
			builder.addStatement(ifStatement);
			builder.setLrVal(resRval);
			return builder.build();
			// return new ExpressionResult(stmt, resRval, decl, auxVars, overappr);
		}
		case IASTBinaryExpression.op_logicalOr: {
			final ExpressionResult rl = leftOperand.switchToRValueIfNecessary(main, loc, node);
			final ExpressionResult rr = rightOperand.switchToRValueIfNecessary(main, loc, node);
			rl.rexIntToBoolIfNecessary(loc, mExpressionTranslation, mMemoryHandler);
			rr.rexIntToBoolIfNecessary(loc, mExpressionTranslation, mMemoryHandler);

			final ExpressionResultBuilder builder = new ExpressionResultBuilder();

			// stmt.addAll(rl.mStmt);
			// // NOTE: no rr.stmt
			// decl.addAll(rl.mDecl);
			// decl.addAll(rr.mDecl);
			// auxVars.putAll(rl.mAuxVars);
			// auxVars.putAll(rr.mAuxVars);
			// overappr.addAll(rl.mOverappr);
			// overappr.addAll(rr.mOverappr);
			builder.addAllExceptLrValue(rl);
			// NOTE: do not unconditionally add rr.stmt as it may be short-circuited
			builder.addDeclarations(rr.getDeclarations());
			builder.addAuxVars(rr.getAuxVars());
			builder.addOverapprox(rr.getOverapprs());

			if (rr.mStmt.isEmpty()) {
				// no auxVar in operands, hence no side effects in operands
				// we can directly combine operands with LOGICOR
				final RValue resultValue = new RValue(
						ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR,
								rl.mLrVal.getValue(), rr.mLrVal.getValue()),
						new CPrimitive(CPrimitive.CPrimitives.INT), true);
				builder.setLrVal(resultValue);
				return builder.build();

				// return new ExpressionResult(stmt,
				// new RValue(
				// ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR,
				// rl.mLrVal.getValue(), rr.mLrVal.getValue()),
				// new CPrimitive(CPrimitive.CPrimitives.INT), true),
				// decl, auxVars, overappr);
			}
			// create and add tmp var #t~OR~UID
			final CPrimitive intType = new CPrimitive(CPrimitives.INT);
			// final String resName = mNameHandler.getTempVarUID(SFO.AUXVAR.SHORTCIRCUIT,
			// intType);
			// final VarList tempVar = new VarList(loc, new String[] { resName }, new
			// PrimitiveType(loc, SFO.BOOL));
			// final VariableDeclaration tmpVar =
			// new VariableDeclaration(loc, new Attribute[0], new VarList[] { tempVar });
			// auxVars.put(tmpVar, loc);
			// decl.add(tmpVar);
			final AuxVarInfo resNameAuxvar = AuxVarInfo.constructAuxVarInfo(loc, main, intType,
					new PrimitiveType(loc, BoogieType.TYPE_BOOL, SFO.BOOL), SFO.AUXVAR.SHORTCIRCUIT);
			builder.addDeclaration(resNameAuxvar.getVarDec());
			builder.addAuxVar(resNameAuxvar);

			final RValue tmpRval = new RValue(resNameAuxvar.getExp(), intType, true);
			final RValue resRval = tmpRval;
			// #t~OR~UID = left
			final AssignmentStatement aStat = StatementFactory.constructAssignmentStatement(loc,
					new LeftHandSide[] { resNameAuxvar.getLhs() }, new Expression[] { rl.mLrVal.getValue() });
			// for (final Overapprox overapproxItem : overappr) {
			for (final Overapprox overapproxItem : builder.getOverappr()) {
				overapproxItem.annotate(aStat);
			}
			// stmt.add(aStat);
			builder.addStatement(aStat);
			// if (#t~OR~UID) {} else {#t~OR~UID = right;}
			final ArrayList<Statement> outerElsePart = new ArrayList<>();
			outerElsePart.addAll(rr.mStmt);

			outerElsePart.add(StatementFactory.constructAssignmentStatement(loc,
					new LeftHandSide[] { resNameAuxvar.getLhs() }, new Expression[] { rr.mLrVal.getValue() }));
			final IfStatement ifStatement = new IfStatement(loc, tmpRval.getValue(), new Statement[0],
					outerElsePart.toArray(new Statement[outerElsePart.size()]));
			// for (final Overapprox overapprItem : overappr) {
			for (final Overapprox overapprItem : builder.getOverappr()) {
				overapprItem.annotate(ifStatement);
			}
			// stmt.add(ifStatement);
			builder.addStatement(ifStatement);
			// return new ExpressionResult(stmt, resRval, decl, auxVars, overappr);
			builder.setLrVal(resRval);
			return builder.build();
		}
		case IASTBinaryExpression.op_modulo:
		case IASTBinaryExpression.op_multiply:
		case IASTBinaryExpression.op_divide: {
			final ExpressionResult rl = leftOperand.switchToRValueIfNecessary(main, loc, node);
			final ExpressionResult rr = rightOperand.switchToRValueIfNecessary(main, loc, node);
			rl.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			rr.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			return handleMultiplicativeOperation(main, loc, null, node.getOperator(), rl, rr, node);
		}
		case IASTBinaryExpression.op_moduloAssign:
		case IASTBinaryExpression.op_multiplyAssign:
		case IASTBinaryExpression.op_divideAssign: {
			final ExpressionResult rl = leftOperand.switchToRValueIfNecessary(main, loc, node);
			final ExpressionResult rr = rightOperand.switchToRValueIfNecessary(main, loc, node);
			rl.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			rr.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			return handleMultiplicativeOperation(main, loc, leftOperand.mLrVal, node.getOperator(), rl, rr, node);
		}
		case IASTBinaryExpression.op_plus:
		case IASTBinaryExpression.op_minus: {
			final ExpressionResult rl = leftOperand.switchToRValueIfNecessary(main, loc, node);
			final ExpressionResult rr = rightOperand.switchToRValueIfNecessary(main, loc, node);
			rl.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			rr.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			return handleAdditiveOperation(main, loc, null, node.getOperator(), rl, rr, node);
		}
		case IASTBinaryExpression.op_plusAssign:
		case IASTBinaryExpression.op_minusAssign: {
			final ExpressionResult rl = leftOperand.switchToRValueIfNecessary(main, loc, node);
			final ExpressionResult rr = rightOperand.switchToRValueIfNecessary(main, loc, node);
			rl.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			rr.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			return handleAdditiveOperation(main, loc, leftOperand.mLrVal, node.getOperator(), rl, rr, node);
		}
		case IASTBinaryExpression.op_binaryAnd:
		case IASTBinaryExpression.op_binaryOr:
		case IASTBinaryExpression.op_binaryXor: {
			final ExpressionResult rl = leftOperand.switchToRValueIfNecessary(main, loc, node);
			final ExpressionResult rr = rightOperand.switchToRValueIfNecessary(main, loc, node);
			rl.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			rr.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			return handleBitwiseArithmeticOperation(main, loc, null, node.getOperator(), rl, rr, node);
		}
		case IASTBinaryExpression.op_binaryAndAssign:
		case IASTBinaryExpression.op_binaryOrAssign:
		case IASTBinaryExpression.op_binaryXorAssign: {
			final ExpressionResult rl = leftOperand.switchToRValueIfNecessary(main, loc, node);
			final ExpressionResult rr = rightOperand.switchToRValueIfNecessary(main, loc, node);
			rl.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			rr.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			return handleBitwiseArithmeticOperation(main, loc, leftOperand.mLrVal, node.getOperator(), rl, rr, node);
		}
		case IASTBinaryExpression.op_shiftLeft:
		case IASTBinaryExpression.op_shiftRight: {
			final ExpressionResult rl = leftOperand.switchToRValueIfNecessary(main, loc, node);
			final ExpressionResult rr = rightOperand.switchToRValueIfNecessary(main, loc, node);
			rl.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			rr.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			return handleBitshiftOperation(main, loc, null, node.getOperator(), rl, rr, node);

		}
		case IASTBinaryExpression.op_shiftLeftAssign:
		case IASTBinaryExpression.op_shiftRightAssign: {
			final ExpressionResult rl = leftOperand.switchToRValueIfNecessary(main, loc, node);
			final ExpressionResult rr = rightOperand.switchToRValueIfNecessary(main, loc, node);
			rl.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			rr.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			return handleBitshiftOperation(main, loc, leftOperand.mLrVal, node.getOperator(), rl, rr, node);
		}
		default:
			final String msg = "Unknown or unsupported unary operation";
			throw new UnsupportedSyntaxException(loc, msg);
		}
	}

	/**
	 * Convert an LrValue of array type to an (otherwise equivalent) RValue of pointer type.
	 * <p>
	 * Background: Array expressions can be used in place of pointer expressions in C. (An array may "decay" to a
	 * pointer in C standard terminology.) E.g. when an array is assigned to a pointer variable.
	 *
	 *
	 *
	 * @param rightLrVal
	 * @return
	 */
	public RValue decayArrayLrValToPointer(final ILocation loc, final LRValue rightLrVal, final IASTNode hook) {
		assert rightLrVal.getCType().getUnderlyingType() instanceof CArray;

		final Expression newValue;
		if (isPreRunMode()) {
			if (rightLrVal instanceof HeapLValue) {

				newValue = ((HeapLValue) rightLrVal).getAddress();
				// final Expression oldAddress = ((HeapLValue) rightLrVal).getAddress();
				// newValue = ExpressionFactory.replaceBoogieType(oldAddress, pointerType);
				// address = new RValue(oldAddress,
				// new CPointer(((CArray) rightLrVal.getCType()).getValueType()));
				throw new AssertionError("does this occur??");
			}
			final Expression oldValue = rightLrVal.getValue();
			/*
			 * circumvents Boogie type checking during preprocessing TODO: use type error instead of pointer type?
			 */
			newValue = ExpressionFactory.replaceBoogieType(oldValue, mTypeHandler.getBoogiePointerType());
			((PRDispatcher) mMainDispatcher).moveArrayAndStructIdsOnHeap(loc, rightLrVal.getValue(),
					Collections.emptySet(), hook);
		} else {
			if (rightLrVal instanceof RValueForArrays) {
				newValue = rightLrVal.getValue();
			} else {
				newValue = ((HeapLValue) rightLrVal).getAddress();
			}
		}
		final CType newType = new CPointer(((CArray) rightLrVal.getCType()).getValueType());
		return new RValue(newValue, newType);
	}

	@Override
	public Result visit(final Dispatcher main, final IASTBreakStatement node) {
		final ArrayList<Statement> stmt = new ArrayList<>();
		stmt.add(new BreakStatement(main.getLocationFactory().createCLocation(node)));
		return new ExpressionResult(stmt, null);
	}

	/**
	 * Translate a case statement for use inside a switch statement. C99:6.8.4.2-3: "The expression of each case label
	 * shall be an integer constant expression and no two of the case constant expressions in the same switch statement
	 * shall have the same value after conversion."
	 *
	 */
	@Override
	public Result visit(final Dispatcher main, final IASTCaseStatement node) {
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		ExpressionResult c = (ExpressionResult) main.dispatch(node.getExpression());
		c = c.switchToRValueIfNecessary(main, main.getLocationFactory().createCLocation(node), node);
		mExpressionTranslation.convertIntToInt(loc, c, new CPrimitive(CPrimitives.INT));
		return c;
	}

	@Override
	public Result visit(final Dispatcher main, final IASTCastExpression node) {
		final ILocation loc = main.getLocationFactory().createCLocation(node);

		// TODO: check validity of cast?

		final TypesResult resTypes = (TypesResult) main.dispatch(node.getTypeId().getDeclSpecifier());

		mCurrentDeclaredTypes.push(resTypes);
		final DeclaratorResult declResult = (DeclaratorResult) main.dispatch(node.getTypeId().getAbstractDeclarator());
		final CType newCType = declResult.getDeclaration().getType();
		mCurrentDeclaredTypes.pop();

		ExpressionResult expr = (ExpressionResult) main.dispatch(node.getOperand());
		if (expr.mLrVal.getCType().getUnderlyingType() instanceof CArray
				&& newCType.getUnderlyingType() instanceof CPointer) {
			final RValue newRval = decayArrayLrValToPointer(loc, expr.getLrValue(), node);
			expr.mLrVal = newRval;
		} else {
			expr = expr.switchToRValueIfNecessary(main, loc, node);
		}

		if (POINTER_CAST_IS_UNSUPPORTED_SYNTAX && newCType instanceof CPointer
				&& expr.mLrVal.getCType() instanceof CPointer) {
			final CType newPointsToType = ((CPointer) newCType).pointsToType;
			final CType exprPointsToType = ((CPointer) expr.mLrVal.getCType()).pointsToType;
			if (newPointsToType instanceof CPrimitive && exprPointsToType instanceof CPrimitive) {
				if (((CPrimitive) newPointsToType).getGeneralType() == CPrimitiveCategory.INTTYPE
						&& ((CPrimitive) exprPointsToType).getGeneralType() == CPrimitiveCategory.INTTYPE) {
					final TypeSizes typeSizes = main.getTypeSizes();
					if (typeSizes.isUnsigned((CPrimitive) newPointsToType)
							&& !typeSizes.isUnsigned((CPrimitive) exprPointsToType)
							|| !(typeSizes.isUnsigned((CPrimitive) newPointsToType)
									&& typeSizes.isUnsigned((CPrimitive) exprPointsToType))) {
						throw new UnsupportedSyntaxException(loc, "unsupported cast: " + exprPointsToType
								+ " pointer  to " + newPointsToType + " pointer");
					}

				} else if (((CPrimitive) newPointsToType).getGeneralType() == CPrimitiveCategory.VOID
						&& ((CPrimitive) exprPointsToType).getGeneralType() == CPrimitiveCategory.INTTYPE
						|| ((CPrimitive) newPointsToType).getGeneralType() == CPrimitiveCategory.INTTYPE
								&& ((CPrimitive) exprPointsToType).getGeneralType() == CPrimitiveCategory.VOID) {
					throw new UnsupportedSyntaxException(loc,
							"unsupported cast: " + exprPointsToType + " pointer  to " + newPointsToType + " pointer");
				}
			}
		}

		expr.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
		convert(loc, expr, newCType);
		return expr;
	}

	@Override
	public Result visit(final Dispatcher main, final IASTCompoundStatement node) {
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		// final ArrayList<Declaration> decl = new ArrayList<>();
		// ArrayList<Statement> stmt = new ArrayList<>();
		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
		LRValue expr = null;
		final IASTNode parent = node.getParent();

		if (isNewScopeRequired(parent)) {
			beginScope();
		}

		for (final IASTNode child : node.getChildren()) {
			// checkForACSL(main, resultBuilder.getStatements(),
			// resultBuilder.getDeclarations(), child, null);
			checkForACSL(main, resultBuilder, child, null, true);
			final Result r = main.dispatch(child);
			if (r instanceof ExpressionResult) {
				final ExpressionResult res = (ExpressionResult) r;
				// decl.addAll(res.mDecl);
				// stmt.addAll(res.mStmt);
				resultBuilder.addDeclarations(res.getDeclarations());
				resultBuilder.addStatements(res.getStatements());
				expr = res.mLrVal;
			} else if (r.node != null && r.node instanceof Body) {
				assert false : "should not happen, as CompoundStatement now yields an "
						+ "ExpressionResult or a CompoundStatementExpressionResult";
				// already have a unique naming for variables! --> unfold
				final Body b = (Body) r.node;
				// decl.addAll(Arrays.asList(b.getLocalVars()));
				// stmt.addAll(Arrays.asList(b.getBlock()));
				resultBuilder.addDeclarations(Arrays.asList(b.getLocalVars()));
				resultBuilder.addStatements(Arrays.asList(b.getBlock()));
			} else if (r instanceof SkipResult) {
				// skip
			} else {
				assert false : "should not happen, as CompoundStatement now yields an "
						+ "ExpressionResult or a CompoundStatementExpressionResult";
			}
		}
		// checkForACSL(main, resultBuilder.getStatements(),
		// resultBuilder.getDeclarations(), null, node);
		checkForACSL(main, resultBuilder, null, node, true);
		if (isNewScopeRequired(parent)) {
			// stmt = updateStmtsAndDeclsAtScopeEnd(main, decl, stmt);
			updateStmtsAndDeclsAtScopeEnd(main, resultBuilder, node);

			endScope();
		}
		// return new ExpressionResult(stmt, expr, decl, new LinkedHashSet<>(), new
		// ArrayList<>());
		resultBuilder.setLrVal(expr);
		return resultBuilder.build();
	}

	@Override
	public Result visit(final Dispatcher main, final IASTConditionalExpression node) {
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		assert node.getChildren().length == 3;
		ExpressionResult opCondition = (ExpressionResult) main.dispatch(node.getLogicalConditionExpression());
		opCondition = opCondition.switchToRValueIfNecessary(main, loc, node);
		ExpressionResult opPositive = (ExpressionResult) main.dispatch(node.getPositiveResultExpression());
		opPositive = opPositive.switchToRValueIfNecessary(main, loc, node);
		ExpressionResult opNegative = (ExpressionResult) main.dispatch(node.getNegativeResultExpression());
		opNegative = opNegative.switchToRValueIfNecessary(main, loc, node);
		return handleConditionalOperator(loc, main, opCondition, opPositive, opNegative, node);
	}

	@Override
	public Result visit(final Dispatcher main, final IASTContinueStatement cs) {
		final ILocation loc = main.getLocationFactory().createCLocation(cs);
		final ArrayList<Statement> stmt = new ArrayList<>();
		stmt.add(new GotoStatement(loc, new String[] { mInnerMostLoopLabel.peek() }));
		final ExpressionResult contResult = new ExpressionResult(stmt, null);
		return contResult;
	}

	@Override
	public Result visit(final Dispatcher main, final IASTDeclarationStatement node) {
		return main.dispatch(node.getDeclaration());
	}

	@Override
	public Result visit(final Dispatcher main, final IASTDeclarator node) {
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		final TypesResult resType = mCurrentDeclaredTypes.peek();
		final TypesResult newResType = new TypesResult(resType);

		// are we running the PRDispatcher (PR stands for PreRun)?
		// --> in that case "isOnHeap" has not yet been determined, we set it to false
		newResType.isOnHeap |=
				main instanceof MainDispatcher ? ((MainDispatcher) main).getVariablesForHeap().contains(node) : false;

		final IASTPointerOperator[] pointerOps = node.getPointerOperators();
		for (int i = 0; i < pointerOps.length; i++) {
			newResType.cType = new CPointer(newResType.cType);
		}

		// Adapt the name for multiparse input
		final String declName;

		if (node instanceof IASTArrayDeclarator) {
			final IASTArrayDeclarator arrDecl = (IASTArrayDeclarator) node;

			/*
			 * the innermost type is the value type..
			 */
			CType arrayType = newResType.cType;

			// expression results of from array modifiers
			final ArrayList<ExpressionResult> expressionResults = new ArrayList<>();

			final ListIterator<IASTArrayModifier> it =
					Arrays.asList(arrDecl.getArrayModifiers()).listIterator(arrDecl.getArrayModifiers().length);
			while (it.hasPrevious()) {
				final IASTArrayModifier am = it.previous();
				final RValue sizeFactor;
				if (am.getConstantExpression() != null) {
					// case where we have a number between the brackets,
					// e.g., a[23] or a[n+1]
					ExpressionResult er = (ExpressionResult) main.dispatch(am.getConstantExpression());
					er = er.switchToRValueIfNecessary(main, loc, node);
					// FIXME: 2015-10-25 Matthias: uncomment once the simplification of Boogie
					// expressions is
					// implemented
					mExpressionTranslation.convertIntToInt(loc, er,
							mExpressionTranslation.getCTypeOfPointerComponents());
					expressionResults.add(er);
					sizeFactor = (RValue) er.mLrVal;
				} else if (am.getConstantExpression() == null
						&& arrDecl.getArrayModifiers()[arrDecl.getArrayModifiers().length - 1] == am) {
					// the innermost array modifier may be empty, if there is an initializer; like
					// int a[1][2][] = {...}
					final int intSizeFactor;
					if (arrDecl.getInitializer() != null) {
						if (arrDecl.getInitializer() instanceof IASTEqualsInitializer) {
							intSizeFactor = computeSizeOfInitializer((IASTEqualsInitializer) arrDecl.getInitializer());
						} else {
							throw new UnsupportedOperationException("expected IASTEqualsInitializer");
						}
					} else if (resType.cType instanceof CFunction) {
						// if we have an array of function pointers,
						// the initializer is stored in the parent node
						// 2016-12-31 Matthias: I think this is only a workaround.
						// What if we do not have an array of function pointers
						// but an arrray of pointers to function pointers? Then
						// we probably have to check the parent of the parent
						final IASTFunctionDeclarator fundecl = (IASTFunctionDeclarator) arrDecl.getParent();
						if (fundecl.getInitializer() != null) {
							intSizeFactor = computeSizeOfInitializer((IASTEqualsInitializer) fundecl.getInitializer());
						} else {
							throw new UnsupportedOperationException("expected initializer");
						}
					} else {
						// we have an incomplete array type without an initializer --
						// this may happen in a function parameter..
						intSizeFactor = -1234567;
					}
					final CPrimitive ctype = mExpressionTranslation.getCTypeOfPointerComponents();
					final Expression sizeExpression = mExpressionTranslation.constructLiteralForIntegerType(loc, ctype,
							BigInteger.valueOf(intSizeFactor));
					sizeFactor = new RValue(sizeExpression, ctype, false, false);

				} else {
					throw new IncorrectSyntaxException(loc, "wrong array type in declaration");
				}
				arrayType = new CArray(sizeFactor, arrayType);
			}
			final ExpressionResult allResults = ExpressionResult.copyStmtDeclAuxvarOverapprox(
					expressionResults.toArray(new ExpressionResult[expressionResults.size()]));
			if (!allResults.mDecl.isEmpty() || !allResults.mStmt.isEmpty() || !allResults.mAuxVars.isEmpty()) {
				throw new AssertionError("passing these results is not yet implemented");
			}
			newResType.cType = arrayType;
			declName = mSymbolTable.applyMultiparseRenaming(node.getContainingFilename(), node.getName().toString());
		} else if (node instanceof IASTStandardFunctionDeclarator) {
			final IASTStandardFunctionDeclarator funcDecl = (IASTStandardFunctionDeclarator) node;

			final IASTParameterDeclaration[] paramDecls = funcDecl.getParameters();
			CDeclaration[] paramsParsed = new CDeclaration[paramDecls.length];
			for (int i = 0; i < paramDecls.length; i++) {
				final DeclaratorResult decl = (DeclaratorResult) main.dispatch(paramDecls[i]);
				if (decl.getDeclaration().getName() == "" && decl.getDeclaration().getType() instanceof CPrimitive
						&& ((CPrimitive) decl.getDeclaration().getType()).getType().equals(CPrimitives.VOID)) {
					assert paramDecls.length == 1;
					paramsParsed = new CDeclaration[0];
					break;
				}
				paramsParsed[i] = decl.getDeclaration();
			}
			final CFunction funcType = new CFunction(newResType.cType, paramsParsed, funcDecl.takesVarArgs());
			newResType.cType = funcType;

			declName = mSymbolTable.applyMultiparseRenaming(node.getContainingFilename(), node.getName().toString());
		} else if (node instanceof ICASTKnRFunctionDeclarator) {
			final ICASTKnRFunctionDeclarator funcDecl = (ICASTKnRFunctionDeclarator) node;

			assert funcDecl.getParameterDeclarations().length == funcDecl
					.getParameterNames().length : "implicit int declarations are forbidden from C99 on, this is one, right?";

			final CDeclaration[] paramsParsed = new CDeclaration[funcDecl.getParameterDeclarations().length];
			for (int i = 0; i < funcDecl.getParameterDeclarations().length; i++) {
				final DeclarationResult paramDeclRes =
						(DeclarationResult) main.dispatch(funcDecl.getParameterDeclarations()[i]);
				assert paramDeclRes.getDeclarations().size() == 1;
				paramsParsed[i] = paramDeclRes.getDeclarations().get(0);
			}

			final CFunction funcType = new CFunction(newResType.cType, paramsParsed, false);
			newResType.cType = funcType;
			declName = mSymbolTable.applyMultiparseRenaming(node.getContainingFilename(), node.getName().toString());
		} else {
			// Check if this is a global variable
			if (node.getParent().getParent() instanceof IASTTranslationUnit) {
				declName =
						mSymbolTable.applyMultiparseRenaming(node.getContainingFilename(), node.getName().toString());
			} else {
				declName = node.getName().toString();
			}
		}
		final int bitfieldSize;
		if (node instanceof IASTFieldDeclarator) {
			final IASTExpression expr = ((IASTFieldDeclarator) node).getBitFieldSize();
			bitfieldSize = Integer.parseInt(expr.getRawSignature());
		} else {
			// we use -1 to indicate that this is no bitfield
			bitfieldSize = -1;
		}
		if (node.getNestedDeclarator() != null) {
			mCurrentDeclaredTypes.push(newResType);
			DeclaratorResult result = (DeclaratorResult) main.dispatch(node.getNestedDeclarator());
			mCurrentDeclaredTypes.pop();
			if (node.getInitializer() != null) {
				final CDeclaration cdec = result.getDeclaration();
				result = new DeclaratorResult(new CDeclaration(cdec.getType(), cdec.getName(), node.getInitializer(),
						null, cdec.isOnHeap(), CStorageClass.UNSPECIFIED, bitfieldSize));
			}
			return result;
		}
		final DeclaratorResult result = new DeclaratorResult(new CDeclaration(newResType.cType, declName,
				node.getInitializer(), null, newResType.isOnHeap, CStorageClass.UNSPECIFIED, bitfieldSize));
		return result;
	}

	@Override
	public Result visit(final Dispatcher main, final IASTDefaultStatement node) {
		final ArrayList<Statement> stmt = new ArrayList<>();
		final ArrayList<Declaration> decl = new ArrayList<>();
		// final Map<VariableDeclaration, ILocation> emptyAuxVars = new
		// LinkedHashMap<>(0);
		final Set<AuxVarInfo> emptyAuxVars = new LinkedHashSet<>(0);
		final List<Overapprox> overappr = new ArrayList<>();
		return new ExpressionResult(stmt,
				new RValue(
						ExpressionFactory.createBooleanLiteral(main.getLocationFactory().createCLocation(node), true),
						new CPrimitive(CPrimitives.INT)),
				decl, emptyAuxVars, overappr);
	}

	@Override
	public Result visit(final Dispatcher main, final IASTDoStatement node) {
		final ExpressionResult condResult = (ExpressionResult) main.dispatch(node.getCondition());
		final String loopLabel = mNameHandler.getGloballyUniqueIdentifier(SFO.LOOPLABEL);
		mInnerMostLoopLabel.push(loopLabel);
		final Result bodyResult = main.dispatch(node.getBody());
		mInnerMostLoopLabel.pop();
		final LoopInvariantSpecification witnessInvariant = fetchWitnessInvariantAtLoop(main, node);
		return handleLoops(main, node, bodyResult, condResult, loopLabel, witnessInvariant);
	}

	@Override
	public Result visit(final Dispatcher main, final IASTEqualsInitializer node) {
		return main.dispatch(node.getInitializerClause());
	}

	@Override
	public Result visit(final Dispatcher main, final IASTExpressionList node) {
		final ExpressionListResult result = new ExpressionListResult();
		for (final IASTExpression expr : node.getExpressions()) {
			final Result r = main.dispatch(expr);
			assert r instanceof ExpressionResult;
			result.list.add((ExpressionResult) r);
		}
		return result;
	}

	@Override
	public Result visit(final Dispatcher main, final IASTExpressionStatement node) {
		final Result r = main.dispatch(node.getExpression());
		if (r instanceof ExpressionResult) {
			final ExpressionResult rExp = (ExpressionResult) r;

			final ArrayList<Statement> stmt = new ArrayList<>(rExp.mStmt);
			final ArrayList<Declaration> decl = new ArrayList<>(rExp.mDecl);
			final List<Overapprox> overappr = new ArrayList<>();

			stmt.addAll(CTranslationUtil.createHavocsForAuxVars(rExp.getAuxVars()));
			overappr.addAll(rExp.mOverappr);
			return new ExpressionResult(stmt, rExp.mLrVal, decl, Collections.emptySet(), overappr);
		} else if (r instanceof ExpressionListResult) {
			final ArrayList<Statement> stmt = new ArrayList<>();
			final ArrayList<Declaration> decl = new ArrayList<>();
			final List<Overapprox> overappr = new ArrayList<>();
			// final Map<VariableDeclaration, ILocation> emptyAuxVars = new
			// LinkedHashMap<>(0);
			for (final ExpressionResult res : ((ExpressionListResult) r).list) {
				if (!res.mStmt.isEmpty()) {
					stmt.addAll(res.mStmt);
					decl.addAll(res.mDecl);
					stmt.addAll(CTranslationUtil.createHavocsForAuxVars(res.getAuxVars()));
					overappr.addAll(res.mOverappr);
				}
			}

			return new ExpressionResult(stmt, null, decl, Collections.emptySet(), overappr);
		} else if (r instanceof SkipResult) {
			return r;
		}
		final String msg = "We always convert to AssignmentStatement, other options raise this error!";
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		throw new UnsupportedSyntaxException(loc, msg);
	}

	@Override
	public Result visit(final Dispatcher main, final IASTFieldReference node) {
		return mStructHandler.handleFieldReference(main, node);
	}

	@Override
	public Result visit(final Dispatcher main, final IASTForStatement node) {
		final String loopLabel = mNameHandler.getGloballyUniqueIdentifier(SFO.LOOPLABEL);
		final LoopInvariantSpecification witnessInvariant = fetchWitnessInvariantAtLoop(main, node);
		return handleLoops(main, node, null, null, loopLabel, witnessInvariant);
	}

	@Override
	public Result visit(final Dispatcher main, final IASTFunctionCallExpression node) {
		final IASTExpression functionName = node.getFunctionNameExpression();
		if (functionName instanceof IASTIdExpression) {
			// Transform the name for multifile input
			final String transformedName = mSymbolTable.applyMultiparseRenaming(node.getContainingFilename(),
					((IASTIdExpression) functionName).getName().toString()); // TODO inject this, but is this really
																				// needed?
			final Result standardFunction =
					mStandardFunctionHandler.translateStandardFunction(main, node, (IASTIdExpression) functionName);

			if (standardFunction != null) {
				return standardFunction;
			}
		}
		final Check check = new Check(Check.Spec.PRE_CONDITION);
		final ILocation loc = main.getLocationFactory().createCLocation(node, check);
		return mFunctionHandler.handleFunctionCallExpression(main, mMemoryHandler, mStructHandler, loc, functionName,
				node.getArguments());
	}

	@Override
	public Result visit(final Dispatcher main, final IASTFunctionDefinition node) {
		if (!main.isReachable(node)) {
			// Unreachable function declaration. Test for parent=TU skipped: Not necessary, right?
			return new SkipResult();
		}

		final TypesResult resType = (TypesResult) main.dispatch(node.getDeclSpecifier());

		mCurrentDeclaredTypes.push(resType);
		final DeclaratorResult declResult = (DeclaratorResult) main.dispatch(node.getDeclarator());
		mCurrentDeclaredTypes.pop();
		assert declResult.getDeclaration().getType() instanceof CFunction;
		return mFunctionHandler.handleFunctionDefinition(main, mMemoryHandler, node, declResult.getDeclaration(),
				mContract);
	}

	@Override
	public Result visit(final Dispatcher main, final IASTGotoStatement node) {
		final ArrayList<Statement> stmt = new ArrayList<>();
		if (main instanceof MainDispatcher) {
			final AssertStatement assertWitnessInvariant = ((MainDispatcher) main).fetchInvariantAtGoto(node);
			if (assertWitnessInvariant != null) {
				stmt.add(assertWitnessInvariant);
			}
		}
		final String[] name = new String[] { node.getName().toString() };
		stmt.add(new GotoStatement(main.getLocationFactory().createCLocation(node), name));
		return new ExpressionResult(stmt, null);
	}

	@Override
	public Result visit(final Dispatcher main, final IASTIdExpression node) {
		final ILocation loc = main.getLocationFactory().createCLocation(node);

		// Apply multifile input prefixing transformations to the ID
		final String cId = node.getName().toString();
		final String cIdMp = mSymbolTable.applyMultiparseRenaming(node.getContainingFilename(), cId);

		// deal with builtin constants
		if ("NULL".equals(cId)) {
			return new ExpressionResult(new RValue(mExpressionTranslation.constructNullPointer(loc),
					new CPointer(new CPrimitive(CPrimitives.VOID))));

		} else if ("__PRETTY_FUNCTION__".equals(cId) || "__FUNCTION__".equals(cId)) {
			// TODO: Was only in SvComp14Handler, but seems useful anywhere
			final CType returnType = new CPointer(new CPrimitive(CPrimitives.CHAR));
			// final String tId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.NONDET,
			// returnType);
			// final VariableDeclaration tVarDecl = new VariableDeclaration(loc, new
			// Attribute[0], new VarList[] {
			// new VarList(loc, new String[] { tId },
			// main.mTypeHandler.constructPointerType(loc)) });
			final AuxVarInfo auxvar = AuxVarInfo.constructAuxVarInfo(loc, main, returnType, SFO.AUXVAR.NONDET);
			final RValue rvalue = new RValue(auxvar.getExp(), returnType);
			final ArrayList<Declaration> decls = new ArrayList<>();
			decls.add(auxvar.getVarDec());
			// final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
			// auxVars.put(auxvar.getVarDec(), loc);
			return new ExpressionResult(new ArrayList<Statement>(), rvalue, decls, Collections.singleton(auxvar));
		} else if (!mSymbolTable.containsCSymbol(node, cIdMp)
				&& ("NAN".equals(cId) || "INFINITY".equals(cId) || "inf".equals(cId))) {
			final ExpressionResult result = mExpressionTranslation.createNanOrInfinity(loc, cId);
			return result;
		} else if (mExpressionTranslation.isNumberClassificationMacro(cId)) {
			final RValue rvalue = mExpressionTranslation.handleNumberClassificationMacro(loc, cId);
			return new ExpressionResult(rvalue);
		} else if ("__func__".equals(cId)) {
			final CType cType = new CPointer(new CPrimitive(CPrimitives.CHAR));
			// final String tId = mNameHandler.getTempVarUID(SFO.AUXVAR.NONDET, cType);
			// final VariableDeclaration tVarDecl = new VariableDeclaration(loc, new
			// Attribute[0],
			// new VarList[] { new VarList(loc, new String[] { tId },
			// mTypeHandler.constructPointerType(loc)) });
			final AuxVarInfo auxvar = AuxVarInfo.constructAuxVarInfo(loc, main, cType, SFO.AUXVAR.NONDET);
			final RValue rvalue = new RValue(auxvar.getExp(), cType);
			final ArrayList<Declaration> decls = new ArrayList<>();
			decls.add(auxvar.getVarDec());
			// final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
			// auxVars.put(auxvar.getVarDec(), loc);
			return new ExpressionResult(new ArrayList<Statement>(), rvalue, decls, Collections.singleton(auxvar));
		}

		final String bId;
		final CType cType;
		final boolean useHeap;
		final boolean intFromPtr;
		DeclarationInformation declarationInformation;

		if (mSymbolTable.containsCSymbol(node, cIdMp) && !mProcedureManager.hasProcedure(cIdMp)) {
			// we have a normal variable
			final SymbolTableValue stv = mSymbolTable.findCSymbol(node, cIdMp);
			bId = stv.getBoogieName();
			cType = stv.getCVariable();
			useHeap = isHeapVar(bId);
			intFromPtr = stv.isIntFromPointer();
			declarationInformation = stv.getDeclarationInformation();
			// } else if (mFunctionHandler.getProcedures().keySet().contains(cId)) {
		} else if (mProcedureManager.hasProcedure(cIdMp)) {
			// C11 6.3.2.1.4 says: A function designator is an expression that
			// has function type.
			final CFunction cFunction = mProcedureManager.getCFunctionType(cIdMp);
			cType = cFunction;
			bId = SFO.FUNCTION_ADDRESS + cIdMp;
			useHeap = true;
			intFromPtr = false;
			declarationInformation = DeclarationInformation.DECLARATIONINFO_GLOBAL;
		} else if (main.getFunctionToIndex().containsKey(cIdMp)) {
			throw new AssertionError("function not known to function handler");
		} else {
			throw new UnsupportedSyntaxException(loc,
					"identifier is not declared (neither a variable nor a function name): " + cId + " in file "
							+ node.getContainingFilename());
		}

		BoogieType boogieType;
		{
			final ASTType astType = mTypeHandler.cType2AstType(loc, cType);
			boogieType = mBoogieTypeHelper.getBoogieTypeForBoogieASTType(astType);
		}

		LRValue lrVal = null;
		if (useHeap) {
			final IdentifierExpression idExp = // new IdentifierExpression(loc, bId);
					ExpressionFactory.constructIdentifierExpression(loc, mTypeHandler.getBoogiePointerType(), bId,
							declarationInformation);
			// convention: the ctype in the symbol table of something that we put on the
			// heap
			// is the same as it would be if we did not put it on heap
			lrVal = LRValueFactory.constructHeapLValue(main, idExp, cType, intFromPtr, null);
		} else {
			final VariableLHS idLhs = // new VariableLHS(loc, bId);
					ExpressionFactory.constructVariableLHS(loc, boogieType, bId, declarationInformation);
			lrVal = new LocalLValue(idLhs, cType, false, intFromPtr, null);
		}
		return new ExpressionResult(lrVal);
	}

	@Override
	public Result visit(final Dispatcher main, final IASTIfStatement node) {
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		final ArrayList<Declaration> decl = new ArrayList<>();
		final ArrayList<Statement> stmt = new ArrayList<>();
		final List<Overapprox> overappr = new ArrayList<>();
		// final Map<VariableDeclaration, ILocation> emptyAuxVars = new
		// LinkedHashMap<>();

		ExpressionResult condResult = (ExpressionResult) main.dispatch(node.getConditionExpression());
		condResult = condResult.switchToRValueIfNecessary(main, loc, node);
		condResult.rexIntToBoolIfNecessary(loc, mExpressionTranslation, mMemoryHandler);
		final RValue cond = (RValue) condResult.mLrVal;
		decl.addAll(condResult.mDecl);
		stmt.addAll(condResult.mStmt);
		overappr.addAll(condResult.mOverappr);
		final List<HavocStatement> havocs = CTranslationUtil.createHavocsForAuxVars(condResult.getAuxVars());

		final Result thenResult = main.dispatch(node.getThenClause());
		final List<Statement> thenStmt = new ArrayList<>();
		thenStmt.addAll(havocs);
		if (thenResult instanceof ExpressionResult) {
			final ExpressionResult re = (ExpressionResult) thenResult;
			decl.addAll(re.mDecl);
			thenStmt.addAll(re.mStmt);
		} else if (thenResult != null) {
			if (thenResult.node instanceof Body) {
				final Body thenPart = (Body) thenResult.node;
				thenStmt.addAll(Arrays.asList(thenPart.getBlock()));
				decl.addAll(Arrays.asList(thenPart.getLocalVars()));
			} else if (thenResult instanceof SkipResult) {
				// add no statements or declarations
			} else {
				final String msg = "Error: unexpected dispatch result";
				throw new IncorrectSyntaxException(loc, msg);
			}
		}

		final List<Statement> elseStmt = new ArrayList<>();
		elseStmt.addAll(havocs);
		if (node.getElseClause() != null) {
			final Result elseResult = main.dispatch(node.getElseClause());
			if (elseResult instanceof ExpressionResult) {
				final ExpressionResult re = (ExpressionResult) elseResult;
				decl.addAll(re.mDecl);
				elseStmt.addAll(re.mStmt);
			} else if (elseResult != null) {
				if (elseResult.node instanceof Body) {
					final Body elsePart = (Body) elseResult.node;
					elseStmt.addAll(Arrays.asList(elsePart.getBlock()));
					decl.addAll(Arrays.asList(elsePart.getLocalVars()));
				}
			} else {
				final String msg = "Error: unexpected dispatch result";
				throw new IncorrectSyntaxException(loc, msg);
			}
		}
		assert thenStmt != null;
		assert elseStmt != null;
		// TODO : handle if(pointer), if(pointer==NULL) and if(pointer==0)
		final IfStatement ifStmt = new IfStatement(loc, cond.getValue(),
				thenStmt.toArray(new Statement[thenStmt.size()]), elseStmt.toArray(new Statement[elseStmt.size()]));
		for (final Overapprox overapprItem : overappr) {
			overapprItem.annotate(ifStmt);
		}
		stmt.add(ifStmt);
		return new ExpressionResult(stmt, null, decl, Collections.emptySet(), overappr);
	}

	@Override
	public Result visit(final Dispatcher main, final IASTInitializerClause node) {
		assert node.getChildren().length == 1;
		final Result r = main.dispatch(node.getChildren()[0]);
		assert r instanceof ExpressionResult;
		final ExpressionResult rex = (ExpressionResult) r;
		return rex.switchToRValueIfNecessary(main, main.getLocationFactory().createCLocation(node), node);
	}

	@Override
	public Result visit(final Dispatcher main, final IASTInitializerList node) {
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		if (node.getClauses().length != node.getSize()) {
			throw new IllegalArgumentException("You might have parsed your code with "
					+ "ITranslationUnit.AST_SKIP_TRIVIAL_EXPRESSIONS_IN_AGGREGATE_INITIALIZERS!");
		}
		final InitializerResultBuilder result = new InitializerResultBuilder();
		for (final IASTInitializerClause i : node.getClauses()) {
			final Result r = main.dispatch(i);
			if (r instanceof InitializerResult) {
				result.addChild((InitializerResult) r);
			} else if (r instanceof ExpressionResult) {
				ExpressionResult rex = (ExpressionResult) r;
				// TODO: (alex, feb 2018) quite unsure about always doing this array to pointer conversion..
				rex = rex.decayArrayToPointerIfNecessary(main, loc, node);
				rex = rex.switchToRValueIfNecessary(main, loc, node);
				result.addChild(new InitializerResultBuilder().setRootExpressionResult(rex).build());

			} else {
				final String msg = "Unexpected result";
				throw new UnsupportedSyntaxException(loc, msg);
			}
		}
		return result.build();
	}

	@Override
	public Result visit(final Dispatcher main, final IASTLabelStatement node) {
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		final ArrayList<Statement> stmt = new ArrayList<>();
		final ArrayList<Declaration> decl = new ArrayList<>();
		// final Map<VariableDeclaration, ILocation> emptyAuxVars = new
		// LinkedHashMap<>(0);
		final List<Overapprox> overappr = new ArrayList<>();
		final String label = node.getName().toString();
		if (mErrorLabelWarning && "ERROR".equals(label)) {
			final String longDescription =
					"The label \"ERROR\" does not have a special meaning in the translation mode you selected. You might want to change your settings and use the SV-COMP translation mode.";
			main.warn(loc, longDescription);
		}
		stmt.add(new Label(loc, label));
		final Result r = main.dispatch(node.getNestedStatement());
		if (r instanceof ExpressionResult) {
			final ExpressionResult res = (ExpressionResult) r;
			decl.addAll(res.mDecl);
			stmt.addAll(res.mStmt);
			overappr.addAll(res.mOverappr);
			return new ExpressionResult(stmt, res.mLrVal, decl, Collections.emptySet(), overappr);
		} else if (r instanceof SkipResult) {
			return new ExpressionResult(stmt, null, decl, Collections.emptySet());
		} else { // r instanceof Result ...
			RValue expr = null;
			if (r.node instanceof Statement) {
				stmt.add((Statement) r.node);
			} else if (r.node instanceof Declaration) {
				decl.add((Declaration) r.node);
			} else if (r.node instanceof Expression) {
				expr = new RValue((Expression) r.node, null);// FIXME ??
			} else if (r.node instanceof Body) {
				// we already have a unique naming for variables! --> unfold
				final Body b = (Body) r.node;
				decl.addAll(Arrays.asList(b.getLocalVars()));
				stmt.addAll(Arrays.asList(b.getBlock()));
			} else {
				final String msg = "Unexpected boogie AST node type: " + r.node.getClass();
				throw new UnsupportedSyntaxException(loc, msg);
			}
			return new ExpressionResult(stmt, expr, decl, Collections.emptySet());
		}
	}

	@Override
	public Result visit(final Dispatcher main, final IASTLiteralExpression node) {
		return mExpressionTranslation.translateLiteral(main, node);
	}

	@Override
	public Result visit(final Dispatcher main, final IASTNode node) {
		final String msg = "CHandler: Not yet implemented: \"" + node.getRawSignature() + "\" (Type: "
				+ node.getClass().getName() + ")";
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		throw new UnsupportedSyntaxException(loc, msg);
	}

	@Override
	public Result visit(final Dispatcher main, final IASTNullStatement node) {
		return new SkipResult();
	}

	@Override
	public Result visit(final Dispatcher main, final IASTParameterDeclaration node) {
		final TypesResult resType = (TypesResult) main.dispatch(node.getDeclSpecifier());

		mCurrentDeclaredTypes.push(resType);
		final DeclaratorResult declResult = (DeclaratorResult) main.dispatch(node.getDeclarator());
		mCurrentDeclaredTypes.pop();
		return declResult;
	}

	@Override
	public Result visit(final Dispatcher main, final IASTPointer node) {
		// TODO : implement pointer IASTPointer? When is this required?!
		throw new UnsupportedOperationException("This should have been handled before ...");
	}

	@Override
	public Result visit(final Dispatcher main, final IASTProblem node) {
		final String msg = "Syntax error in C program: " + node.getMessage();
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		throw new IncorrectSyntaxException(loc, msg);
	}

	@Override
	public Result visit(final Dispatcher main, final IASTProblemDeclaration node) {
		final String msg = "Syntax error (declaration problem) in C program: " + node.getProblem().getMessage();
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		throw new IncorrectSyntaxException(loc, msg);
	}

	@Override
	public Result visit(final Dispatcher main, final IASTProblemExpression node) {
		final String msg = "Syntax error (expression problem) in C program: " + node.getProblem().getMessage();
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		throw new IncorrectSyntaxException(loc, msg);
	}

	@Override
	public Result visit(final Dispatcher main, final IASTProblemStatement node) {
		final String msg = "Syntax error (statement problem) in C program: " + node.getProblem().getMessage();
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		throw new IncorrectSyntaxException(loc, msg);
	}

	@Override
	public Result visit(final Dispatcher main, final IASTProblemTypeId node) {
		final String msg = "Syntax error (type ID problem) in C program: " + node.getProblem().getMessage();
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		throw new IncorrectSyntaxException(loc, msg);
	}

	@Override
	public Result visit(final Dispatcher main, final IASTReturnStatement node) {
		return mFunctionHandler.handleReturnStatement(main, mMemoryHandler, mStructHandler, node);
	}

	/**
	 * Visit the SimpleDeclaration (which may be quite complex in fact..). The return value here may have different
	 * uses:
	 * <li>for global variables and declarations inside of struct definitions, it is a ResultDeclaration (containing the
	 * Boogie Declaration of the variable)
	 * <li>for local variables that have an initializer, a ResultExpression is returned which contains (Boogie)
	 * statements and declarations that make the initialization according to the initializer
	 * <li>for local variables without an initializer, a havoc statement is inserted into the ResultExpression instead
	 * The declarations themselves of the local variables (and f.i. typedefs) are stored in the symbolTable and inserted
	 * into the Boogie code at the next endScope()
	 * <p>
	 * Declarations of static variables are added to mDeclarationsGlobalInBoogie such that they can be declared and
	 * initialized globally.
	 * <p>
	 * Variables/types that are global in Boogie but not in C are stored in the Symboltable to keep the association of
	 * BoogieId and CId.
	 */
	@Override
	public Result visit(final Dispatcher main, final IASTSimpleDeclaration node) {
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		if (node.getParent() instanceof IASTTranslationUnit && !main.isReachable(node)) {
			// Unreachable global declaration.
			return new SkipResult();
		}

		/*
		 * not sure what it means when the declspecifier is null ..
		 */
		if (node.getDeclSpecifier() == null) {
			final String msg = "This statement can be removed!";
			main.warn(loc, msg);
			return new SkipResult();
		}

		/*
		 * we have an enum declaration
		 */
		if (node.getDeclSpecifier() instanceof IASTEnumerationSpecifier) {
			handleEnumDeclaration(main, node);
		}

		/*
		 * obtain type information from the DeclSpecifier
		 */
		final Result declSpecifierResult = main.dispatch(node.getDeclSpecifier());
		assert declSpecifierResult instanceof SkipResult || declSpecifierResult instanceof TypesResult;

		if (declSpecifierResult instanceof SkipResult) {
			return declSpecifierResult;
		}

		if (declSpecifierResult instanceof TypesResult) {
			final TypesResult resType = (TypesResult) declSpecifierResult;
			Result result = new SkipResult(); // Skip will be overwritten in
												// case of a global or a local
												// initialized variable

			final CStorageClass storageClass = scConstant2StorageClass(node.getDeclSpecifier().getStorageClass());

			mCurrentDeclaredTypes.push(resType);
			/**
			 * Christian: C allows several declarations of "similar" types in one go. For instance:
			 * <code>int a, b[2];</code> Here <code>a</code> has type <code>int</code> and <code>b</code> has type
			 * <code>int[]</code>. To solve this, the declaration items are visited one after another.
			 */
			for (final IASTDeclarator d : node.getDeclarators()) {
				// if (d instanceof IASTFieldDeclarator)
				// throw new UnsupportedSyntaxException(loc, "bitfields are not supported at the
				// moment");

				final DeclaratorResult declResult = (DeclaratorResult) main.dispatch(d);

				final CDeclaration cDec = declResult.getDeclaration();
				cDec.setStorageClass(storageClass);

				// are we in prerun mode?
				// if (main instanceof PRDispatcher) {
				if (isPreRunMode()) {
					// all unions should be on heap
					if (cDec.getType().getUnderlyingType() instanceof CUnion && storageClass != CStorageClass.TYPEDEF) {
						((PRDispatcher) main).addToVariablesOnHeap(d);
					}
				}

				///////////////////
				// update symbol table

				// functions keep their cId, and their declaration is not stored
				// in the symbolTable but in
				// FunctionHandler.procedures.
				if (cDec.getType() instanceof CFunction && storageClass != CStorageClass.TYPEDEF) {
					// update functionHandler.procedures instead of symbol table
					mFunctionHandler.handleFunctionDeclarator(main, main.getLocationFactory().createCLocation(d),
							mContract, cDec, d);
					continue;
				}

				// if the same variable is declared multiple times (within the same scope), we
				// only keep one declaration
				// if one of them has an initializer, we keep that one.
				// if we are inside a struct declaration however, this does not apply, we
				// proceed as normal, as the
				// result
				// is needed to build the struct type
				if (!mTypeHandler.isStructDeclaration()) {
					final SymbolTableValue stv = mSymbolTable.findCSymbolInInnermostScope(d, cDec.getName());
					if (stv != null) {
						if (!stv.getCDecl().hasInitializer() || cDec.hasInitializer()) {
							// Keep the last STV with an initializer
							if (mProcedureManager.isGlobalScope() && !mTypeHandler.isStructDeclaration()) {
								// mDeclarationsGlobalInBoogie.remove(mSymbolTable.get(cDec.getName(),
								// loc).getBoogieDecl());
								mStaticObjectsHandler
										.removeDeclaration(mSymbolTable.findCSymbol(d, cDec.getName()).getBoogieDecl());
							}
						}
					}
				}

				final boolean onHeap = cDec.isOnHeap();
				final String bId = mNameHandler.getUniqueIdentifier(node, cDec.getName(), mSymbolTable.getCScopeId(d),
						onHeap, cDec.getType());
				if (onHeap) {
					mBoogieIdsOfHeapVars.add(bId);
				}

				Declaration boogieDec = null;
				// boolean globalInBoogie = false;
				final DeclarationInformation dummyDeclInfo = DeclarationInformation.DECLARATIONINFO_GLOBAL;

				// this .put() is only to have a minimal symbolTableEntry
				// (containing boogieID) for
				// translation of the initializer
				mSymbolTable.storeCSymbol(d, cDec.getName(),
						new SymbolTableValue(bId, boogieDec, cDec, dummyDeclInfo, d, false));
				cDec.translateInitializer(main);

				ASTType translatedType = null;
				if (onHeap) {
					translatedType = mTypeHandler.constructPointerType(loc);
				} else {
					translatedType = mTypeHandler.cType2AstType(loc, cDec.getType());
				}

				final DeclarationInformation declarationInformation;
				if (storageClass == CStorageClass.TYPEDEF) {
					boogieDec = new TypeDeclaration(loc, new Attribute[0], false, bId, new String[0], translatedType);

					final BoogieType boogieType = mBoogieTypeHelper.getBoogieTypeForCType(cDec.getType());

					mTypeHandler.addDefinedType(bId, new TypesResult(
							new NamedType(loc, boogieType, cDec.getName(), null), false, false, cDec.getType()));
					// TODO: add a sizeof-constant for the type??
					// globalInBoogie = true;
					declarationInformation = DeclarationInformation.DECLARATIONINFO_GLOBAL;
					// mDeclarationsGlobalInBoogie.put(boogieDec, cDec);
					mStaticObjectsHandler.addGlobalTypeDeclaration((TypeDeclaration) boogieDec, cDec);
				} else if (storageClass == CStorageClass.STATIC && !mProcedureManager.isGlobalScope()) {
					// we have a local static variable -> special treatment
					// global static variables are treated like normal global variables..
					boogieDec = new VariableDeclaration(loc, new Attribute[0],
							new VarList[] { new VarList(loc, new String[] { bId }, translatedType) });
					// globalInBoogie = true;
					declarationInformation = DeclarationInformation.DECLARATIONINFO_GLOBAL;
					// mDeclarationsGlobalInBoogie.put(boogieDec, cDec);
					mStaticObjectsHandler.addGlobalVariableDeclaration((VariableDeclaration) boogieDec, cDec);
				} else {
					if (mProcedureManager.isGlobalScope()) {
						declarationInformation = DeclarationInformation.DECLARATIONINFO_GLOBAL;
					} else {
						declarationInformation = new DeclarationInformation(StorageClass.LOCAL,
								mProcedureManager.getCurrentProcedureID());
					}
					final BoogieType boogieType =
							mTypeHandler.astTypeToBoogieType(mTypeHandler.cType2AstType(loc, cDec.getType()));

					/**
					 * For Variable length arrays we have a "non-real" initializer which just initializes the aux var
					 * for the array's size. We do not want to treat this like other initializers (call initVar and so).
					 */
					final boolean hasRealInitializer = cDec.hasInitializer()
							&& (!(cDec.getType() instanceof CArray) || cDec.getInitializer() != null);

					if (!hasRealInitializer && !mProcedureManager.isGlobalScope()
							&& !mTypeHandler.isStructDeclaration()) {
						// in case of a local variable declaration without an
						// initializer, we need to insert a
						// havoc statement (because otherwise the variable is
						// always the same within a loop which
						// may lead to unsoundness)
						// ..except if OnHeap. Then it is malloced instead.
						// (--> this is done below this ite-branching by
						// memoryHandler.addVariableToBeMallocedAndFreed(...))
						assert result instanceof SkipResult || result instanceof ExpressionResult;

						if (result instanceof SkipResult) {
							result = new ExpressionResult((LRValue) null);
						}

						final VariableLHS lhs = // new VariableLHS(loc, bId);
								ExpressionFactory.constructVariableLHS(loc, boogieType, bId, declarationInformation);

						if (cDec.hasInitializer()) { // must be a non-real initializer for variable length array size
														// --> need to pass this on
							// TODO: double check this
							((ExpressionResult) result).getDeclarations()
									.addAll(cDec.getInitializer().getRootExpressionResult().getDeclarations());
							((ExpressionResult) result).getStatements()
									.addAll(cDec.getInitializer().getRootExpressionResult().getStatements());
							((ExpressionResult) result).getAuxVars()
									.addAll(cDec.getInitializer().getRootExpressionResult().getAuxVars());
						}

						// no initializer --> essentially needs to be havoced f.i. in each loop
						// iteration
						if (!onHeap) {
							((ExpressionResult) result).mStmt.add(new HavocStatement(loc, new VariableLHS[] { lhs }));
						} else {
							final LocalLValue llVal = new LocalLValue(lhs, cDec.getType(), null);
							// old solution: havoc via an auxvar, new solution (below):
							// just malloc at the right place (much shorter for arrays and structs..)
							((ExpressionResult) result).mStmt.add(mMemoryHandler.getMallocCall(llVal, loc, node));
							mMemoryHandler.addVariableToBeFreed(main,
									new LocalLValueILocationPair(llVal, LocationFactory.createIgnoreLocation(loc)));
						}
					} else if (hasRealInitializer && !mProcedureManager.isGlobalScope()
							&& !mTypeHandler.isStructDeclaration()) {
						// in case of a local variable declaration with an initializer, the statements
						// and delcs
						// necessary for the initialization are the result
						assert result instanceof SkipResult || result instanceof ExpressionResult;
						final VariableLHS lhs = // new VariableLHS(loc, bId);
								ExpressionFactory.constructVariableLHS(loc, boogieType, bId, declarationInformation);
						final ExpressionResult initRex =
								mInitHandler.initialize(loc, main, lhs, cDec.getType(), cDec.getInitializer(), d);
						if (result instanceof SkipResult) {
							result = new ExpressionResult((LRValue) null);
						}

						if (onHeap) {
							final LocalLValue llVal = new LocalLValue(lhs, cDec.getType(), null);
							mMemoryHandler.addVariableToBeFreed(main, new LocalLValueILocationPair(llVal, loc));
							((ExpressionResult) result).mStmt.add(mMemoryHandler.getMallocCall(llVal, loc, node));
						}

						((ExpressionResult) result).mStmt.addAll(initRex.mStmt);
						((ExpressionResult) result).mStmt
								.addAll(CTranslationUtil.createHavocsForAuxVars(initRex.mAuxVars));
						((ExpressionResult) result).mDecl.addAll(initRex.mDecl);
						((ExpressionResult) result).mOverappr.addAll(initRex.mOverappr);
					} else {
						// in case of global variables, the result is the
						// declaration, initialization is
						// done in the postProcessor
						// in case this simpleDeclaration is part of a struct
						// definition, we also need the
						// Declarations as a result
						assert result instanceof SkipResult || result instanceof DeclarationResult;
						if (result instanceof SkipResult) {
							result = new DeclarationResult();
						}
						((DeclarationResult) result).addDeclaration(cDec);
					}
					boogieDec = new VariableDeclaration(loc, new Attribute[0],
							new VarList[] { new VarList(loc, new String[] { bId }, translatedType) });

				}

				// reset the symbol table value with its final contents
				mSymbolTable.storeCSymbol(d, cDec.getName(),
						new SymbolTableValue(bId, boogieDec, cDec, declarationInformation, d, false));
			}
			mCurrentDeclaredTypes.pop();
			return result;
		}
		final String msg = "Unknown result type: " + declSpecifierResult.getClass();
		throw new UnsupportedSyntaxException(loc, msg);
	}

	/**
	 * Translate a switch statement as described in C99: 6.8.4.2
	 */
	@Override
	public Result visit(final Dispatcher main, final IASTSwitchStatement node) {
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();

		// dispatch the controlling expression, convert it to int
		final Result switchParam = main.dispatch(node.getControllerExpression());
		assert switchParam instanceof ExpressionResult;
		final ExpressionResult l =
				((ExpressionResult) switchParam).switchToRValueIfNecessary(main, loc, node.getControllerExpression());
		// 6.8.4.2-1: "The controlling expression of a switch statement shall have integer type."
		// note that this does not mean that it has "int" type, it may be long or char, for instance
		assert l.mLrVal.getCType().isIntegerType();
		// 6.8.4.2-5: "The integer promotions are performed on the controlling
		// expression."
		mExpressionTranslation.doIntegerPromotion(loc, l);

		resultBuilder.addAllExceptLrValue(l);

		final Expression switchArg = l.mLrVal.getValue();

		final CPrimitive intType = new CPrimitive(CPrimitives.INT);
		final String breakLabelName = mNameHandler.getGloballyUniqueIdentifier("SWITCH~BREAK~");

		final AuxVarInfo switchAuxvar = AuxVarInfo.constructAuxVarInfo(loc, main, intType,
				new PrimitiveType(loc, BoogieType.TYPE_BOOL, SFO.BOOL), SFO.AUXVAR.SWITCH);

		resultBuilder.addDeclaration(switchAuxvar.getVarDec());
		resultBuilder.addAuxVar(switchAuxvar);

		boolean isFirst = true;
		boolean firstCond = true;
		Expression cond = null;
		ILocation locC = null;

		ArrayList<Statement> ifBlock = new ArrayList<>();
		beginScope();
		for (final IASTNode child : node.getBody().getChildren()) {
			if (isFirst && !(child instanceof IASTCaseStatement || child instanceof IASTDefaultStatement)) {
				// declarations in the beginning of a switch body (i.e. before the first
				// case/default) are used,
				// statements are dropped
				// see example 6.8.4.2-7

				// we need to dispatch the child in order to fill the symbol table with
				// declarations accordingly
				// the result can only contain statements, which we drop.
				main.dispatch(child);

				continue;
			}
			isFirst = false;

			{
				final ExpressionResultBuilder acslResultBuilder = new ExpressionResultBuilder();
				// checkForACSL(main, ifBlock, resultBuilder.getDeclarations(), child, null,
				// true);
				checkForACSL(main, acslResultBuilder, child, null, true);
				ifBlock.addAll(acslResultBuilder.getStatements());
				resultBuilder.addDeclarations(acslResultBuilder.getDeclarations());
			}

			if (child instanceof IASTCaseStatement || child instanceof IASTDefaultStatement) {
				final ExpressionResult caseExpression = (ExpressionResult) main.dispatch(child);
				if (locC != null) {
					final IfStatement ifStmt = new IfStatement(locC, switchAuxvar.getExp(),
							ifBlock.toArray(new Statement[ifBlock.size()]), new Statement[0]);
					for (final Overapprox overapprItem : caseExpression.mOverappr) {
						overapprItem.annotate(ifStmt);
					}

					if (firstCond) {
						final AssignmentStatement assign = StatementFactory.constructAssignmentStatement(locC,
								new LeftHandSide[] { switchAuxvar.getLhs() }, new Expression[] { cond });
						resultBuilder.addStatement(assign);
						firstCond = false;
					} else {
						final AssignmentStatement assign = StatementFactory.constructAssignmentStatement(locC,
								new LeftHandSide[] { switchAuxvar.getLhs() }, new Expression[] { ExpressionFactory
										.newBinaryExpression(locC, Operator.LOGICOR, switchAuxvar.getExp(), cond) });
						resultBuilder.addStatement(assign);
					}
					resultBuilder.addStatement(ifStmt);
				}

				ifBlock = new ArrayList<>();
				locC = main.getLocationFactory().createCLocation(child);

				if (child instanceof IASTCaseStatement) {
					// 6.8.4.2-5: "The constant expression in each case label is converted to the
					// promoted type of the
					// controlling expression"
					mExpressionTranslation.convertIntToInt(locC, caseExpression, (CPrimitive) l.mLrVal.getCType());
					cond = ExpressionFactory.newBinaryExpression(locC, Operator.COMPEQ, switchArg,
							caseExpression.mLrVal.getValue());
					resultBuilder.addAllExceptLrValue(caseExpression);
				} else {
					// default statement
					cond = caseExpression.mLrVal.getValue();
				}
			} else {
				final Result r = main.dispatch(child);

				if (r instanceof ExpressionResult) {
					final ExpressionResult res = (ExpressionResult) r;
					resultBuilder.addDeclarations(res.getDeclarations());
					resultBuilder.addAuxVars(res.getAuxVars());
					resultBuilder.addOverapprox(res.getOverapprs());
					for (final Statement s : res.mStmt) {
						if (s instanceof BreakStatement) {
							ifBlock.add(new GotoStatement(locC, new String[] { breakLabelName }));
						} else {
							ifBlock.add(s);
						}
					}
				}
				if (r.node != null && r.node instanceof Body) {
					// we already have a unique naming for variables! -> unfold
					final Body b = (Body) r.node;
					resultBuilder.addDeclarations(Arrays.asList(b.getLocalVars()));
					for (final Statement s : b.getBlock()) {
						if (s instanceof BreakStatement) {
							ifBlock.add(new GotoStatement(locC, new String[] { breakLabelName }));
						} else {
							ifBlock.add(s);
						}
					}
				}
			}
		}
		if (locC != null) {
			assert cond != null;
			final IfStatement ifStmt = new IfStatement(locC, switchAuxvar.getExp(),
					ifBlock.toArray(new Statement[ifBlock.size()]), new Statement[0]);
			for (final Overapprox overapprItem : resultBuilder.getOverappr()) {
				overapprItem.annotate(ifStmt);
			}

			if (firstCond) {
				final AssignmentStatement assign = StatementFactory.constructAssignmentStatement(locC,
						new LeftHandSide[] { switchAuxvar.getLhs() }, new Expression[] { cond });
				resultBuilder.addStatement(assign);
				firstCond = false;
			} else {
				final AssignmentStatement assign = StatementFactory.constructAssignmentStatement(locC,
						new LeftHandSide[] { switchAuxvar.getLhs() }, new Expression[] { ExpressionFactory
								.newBinaryExpression(locC, Operator.LOGICOR, switchAuxvar.getExp(), cond) });
				resultBuilder.addStatement(assign);
			}
			resultBuilder.addStatement(ifStmt);
		}
		// checkForACSL(main, resultBuilder.getStatements(),
		// resultBuilder.getDeclarations(), null, node);
		checkForACSL(main, resultBuilder, null, node, true);

		resultBuilder.addStatement(new Label(loc, breakLabelName));
		resultBuilder.addStatements(CTranslationUtil.createHavocsForAuxVars(resultBuilder.getAuxVars()));

		// Use body as hook: This is the scope holder for switch statements! (as controller expression is child of the
		// switch itself and may not have scope access.)
		updateStmtsAndDeclsAtScopeEnd(main, resultBuilder, node.getBody());
		endScope();

		assert resultBuilder.getLrVal() == null;
		return resultBuilder.build();
	}

	@Override
	public Result visit(final Dispatcher main, final IASTTranslationUnit node) {
		for (final IASTPreprocessorStatement preS : node.getAllPreprocessorStatements()) {
			final Result r = main.dispatch(preS);
			if (!(r instanceof SkipResult)) {
				throw new UnsupportedOperationException("Not yet implemented " + preS.toString());
			}
		}
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		try {
			mAcsl = main.nextACSLStatement();
		} catch (final ParseException e1) {
			final String msg = "Skipped a ACSL node due to: " + e1.getMessage();
			main.unsupportedSyntax(loc, msg);
		}

		{
			final ExpressionResultBuilder acslResultBuilder = new ExpressionResultBuilder();
			// TODO(thrax): Check if decl should be passed as null or not.
			// checkForACSL(main, null, decl, node, null);
			checkForACSL(main, acslResultBuilder, node, null, false);
			mDeclarations.addAll(acslResultBuilder.getDeclarations());
		}

		// delayed processing of IASTFunctionDefinitions and structs
		// This is a workaround. Invariants my use global variables that
		// are not yet declared.
		// Better solution: obtain function signature in a first pass
		// process function body in a second pass
		final List<IASTNode> complexNodes = new ArrayList<>();
		for (final IASTNode child : node.getChildren()) {
			// Ignore included declarations which might cause problems
			if (!child.isPartOfTranslationUnitFile()) {
				continue;
			}
			if (child instanceof IASTSimpleDeclaration) {
				final IASTSimpleDeclaration simpleDecl = (IASTSimpleDeclaration) child;
				if (simpleDecl.getDeclSpecifier() instanceof IASTElaboratedTypeSpecifier
						|| simpleDecl.getDeclSpecifier() instanceof ICASTCompositeTypeSpecifier
						|| simpleDecl.getDeclarators().length > 0
								&& simpleDecl.getDeclarators()[0] instanceof CASTFunctionDeclarator
						|| simpleDecl.getDeclSpecifier() instanceof IASTNamedTypeSpecifier) {
					complexNodes.add(child);
				} else {
					processTUchild(main, mDeclarations, child);
				}
			} else if (child instanceof IASTFunctionDefinition) {
				complexNodes.add(child);
			} else {
				processTUchild(main, mDeclarations, child);
			}
		}
		for (final IASTNode funcDef : complexNodes) {
			processTUchild(main, mDeclarations, funcDef);
		}

		// handle global ACSL stuff
		// TODO: do it!

		{
			// TODO(thrax): Check if decl should be passed as null.
			final ExpressionResultBuilder acslResultBuilder = new ExpressionResultBuilder();
			// checkForACSL(main, null, decl, node, null, false);
			checkForACSL(main, acslResultBuilder, node, null, false);
			mDeclarations.addAll(acslResultBuilder.getDeclarations());
		}

		// The declarations (which are needed for the caller) are handled as a member as they
		// do not consist of a Boogie node.
		// So as a workaround null is returned here
		return null;
	}

	@Override
	public Result visit(final Dispatcher main, final IASTTypeIdExpression node) {
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		switch (node.getOperator()) {
		case IASTTypeIdExpression.op_sizeof: {
			final TypesResult rt = (TypesResult) main.dispatch(node.getTypeId().getDeclSpecifier());
			mCurrentDeclaredTypes.push(rt);
			// main.dispatch(node.getTypeId().getAbstractDeclarator());
			final DeclaratorResult dr = (DeclaratorResult) main.dispatch(node.getTypeId().getAbstractDeclarator());
			mCurrentDeclaredTypes.pop();
			// TypesResult checked = checkForPointer(main,
			// node.getTypeId().getAbstractDeclarator().getPointerOperators(),
			// rt, false);

			return new ExpressionResult(
					new RValue(mMemoryHandler.calculateSizeOf(loc, dr.getDeclaration().getType(), node),
							new CPrimitive(CPrimitives.INT)));
		}
		case IASTTypeIdExpression.op_typeof: {
			final TypesResult rt = (TypesResult) main.dispatch(node.getTypeId().getDeclSpecifier());

			mCurrentDeclaredTypes.push(rt);
			final DeclaratorResult dr = (DeclaratorResult) main.dispatch(node.getTypeId().getAbstractDeclarator());
			mCurrentDeclaredTypes.pop();

			return dr;
		}
		default:
			break;
		}
		final String msg = "Unsupported boogie AST node type: " + node.getClass();
		throw new UnsupportedSyntaxException(loc, msg);
	}

	@Override
	public Result visit(final Dispatcher main, final IASTUnaryExpression node) {
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		final ExpressionResult operand = CTranslationUtil.convertExpressionListToExpressionResultIfNecessary(loc, main,
				main.dispatch(node.getOperand()), node);

		// for the cases we know that it's an RValue..

		// final CType oType = operand.mLrVal.getCType().getUnderlyingType();
		// if (oType instanceof CNamed) {
		// oType = ((CNamed) oType).getUnderlyingType();
		// }

		switch (node.getOperator()) {
		case IASTUnaryExpression.op_minus:
		case IASTUnaryExpression.op_not:
		case IASTUnaryExpression.op_plus:
		case IASTUnaryExpression.op_tilde: {
			final ExpressionResult rop = operand.switchToRValueIfNecessary(main, loc, node);
			return handleUnaryArithmeticOperators(main, loc, node.getOperator(), rop, node);
		}
		case IASTUnaryExpression.op_postFixIncr:
		case IASTUnaryExpression.op_postFixDecr: {
			return handlePostfixIncrementAndDecrement(main, loc, node.getOperator(), operand, node);
		}
		case IASTUnaryExpression.op_prefixDecr:
		case IASTUnaryExpression.op_prefixIncr: {
			return handlePrefixIncrementAndDecrement(main, node.getOperator(), loc, operand, node);
		}
		case IASTUnaryExpression.op_bracketedPrimary:
			return operand;
		case IASTUnaryExpression.op_sizeof:
			// final Map<VariableDeclaration, ILocation> emptyAuxVars = new
			// LinkedHashMap<>(0);
			final CType operandType = operand.mLrVal.getCType().getUnderlyingType();
			return new ExpressionResult(
					new RValue(mMemoryHandler.calculateSizeOf(loc, operandType, node), new CPrimitive(CPrimitives.INT)),
					Collections.emptySet());
		case IASTUnaryExpression.op_star: {
			return handleIndirectionOperator(main, operand, loc, node);
		}
		case IASTUnaryExpression.op_amper: {
			return handleAddressOfOperator(main, operand, loc, node);
		}
		case IASTUnaryExpression.op_alignOf:
		default:
			final String msg = "Unknown or unsupported unary operation: " + node.getOperator();
			throw new UnsupportedSyntaxException(loc, msg);
		}
	}

	@Override
	public Result visit(final Dispatcher main, final IASTWhileStatement node) {
		final ExpressionResult condResult = (ExpressionResult) main.dispatch(node.getCondition());
		final String loopLabel = mNameHandler.getGloballyUniqueIdentifier(SFO.LOOPLABEL);
		mInnerMostLoopLabel.push(loopLabel);
		final Result bodyResult = main.dispatch(node.getBody());
		mInnerMostLoopLabel.pop();
		final LoopInvariantSpecification witnessInvariant = fetchWitnessInvariantAtLoop(main, node);
		return handleLoops(main, node, bodyResult, condResult, loopLabel, witnessInvariant);
	}

	@Override
	public Result visit(final Dispatcher main, final IGNUASTCompoundStatementExpression node) {
		return main.dispatch(node.getCompoundStatement());
	}

	/**
	 * @param bId
	 *            Boogie ID
	 */
	public void addBoogieIdsOfHeapVars(final String bId) {
		mBoogieIdsOfHeapVars.add(bId);
	}

	@Override
	public void beginScope() {
		mTypeHandler.beginScope();
		mMemoryHandler.beginScope();
	}

	@Override
	public void endScope() {
		mTypeHandler.endScope();
		mMemoryHandler.endScope();
	}

	@Override
	public TypesResult checkForPointer(final Dispatcher main, final IASTPointerOperator[] pointerOps,
			final TypesResult resType, final boolean putOnHeap) {
		if (putOnHeap || pointerOps.length != 0) {
			// TODO : not sure, if this is enough!
			// There could be multiple PointerOperators (i.e.
			// IASTPointer) - what does that mean for the translation?
			final ASTType t = mTypeHandler.constructPointerType(null);
			final CType cvar = new CPointer(resType.cType);
			return new TypesResult(t, resType.isConst, resType.isVoid, cvar);
		}
		return resType;
	}

	@Override
	public void clearContract() {
		mContract.clear();
	}

	/**
	 * mdeclarationsGlobalInBoogie may contain type declarations that stem from typedefs using an incomplete struct
	 * type. This method is called when the struct type is completed.
	 *
	 * @param cvar
	 * @param incompleteStruct
	 */
	public void completeTypeDeclaration(final CType incompleteStruct, final CType cvar) {
		mStaticObjectsHandler.completeTypeDeclaration(incompleteStruct, cvar, mTypeHandler);
	}

	/*
	 * Matthias 2015-09-21: "premature optimization is the root of all evil" I think, by now we should not use this
	 * method and better live with long expressions. However, I don't want to delete this method, we might want to use
	 * it in the future.
	 */
	@Override
	@Deprecated
	public BigInteger computeConstantValue(final Expression value) {
		if (value instanceof IntegerLiteral) {
			return new BigInteger(((IntegerLiteral) value).getValue());
		} else if (value instanceof UnaryExpression) {
			switch (((UnaryExpression) value).getOperator()) {
			case ARITHNEGATIVE:
				return computeConstantValue(((UnaryExpression) value).getExpr()).negate();
			default:
				throw new UnsupportedOperationException("could not compute constant value");
			}
		} else if (value instanceof BinaryExpression) {
			switch (((BinaryExpression) value).getOperator()) {
			case ARITHDIV:
				return computeConstantValue(((BinaryExpression) value).getLeft())
						.divide(computeConstantValue(((BinaryExpression) value).getRight()));
			case ARITHMINUS:
				return computeConstantValue(((BinaryExpression) value).getLeft())
						.subtract(computeConstantValue(((BinaryExpression) value).getRight()));
			case ARITHMOD:
				return computeConstantValue(((BinaryExpression) value).getLeft())
						.mod(computeConstantValue(((BinaryExpression) value).getRight()));
			case ARITHMUL:
				return computeConstantValue(((BinaryExpression) value).getLeft())
						.multiply(computeConstantValue(((BinaryExpression) value).getRight()));
			case ARITHPLUS:
				return computeConstantValue(((BinaryExpression) value).getLeft())
						.add(computeConstantValue(((BinaryExpression) value).getRight()));
			default:
				throw new UnsupportedOperationException("could not compute constant value");
			}
		} else {
			throw new UnsupportedOperationException("could not compute constant value");
		}
	}

	/**
	 * Handle conversions according to Section 6.3 of C11.
	 *
	 * @param loc
	 * @param rexp
	 * @param newTypeRaw
	 */
	@Override
	public void convert(final ILocation loc, final ExpressionResult rexp, final CType newTypeRaw) {
		final RValue rValIn = (RValue) rexp.mLrVal;
		final CType newType = newTypeRaw.getUnderlyingType();

		final CType oldType = rValIn.getCType().getUnderlyingType();

		final BoogieType oldBoogieType = (BoogieType) rexp.getLrValue().getValue().getType();
		final BoogieType newBoogieType = mBoogieTypeHelper.getBoogieTypeForCType(newTypeRaw);

		if (TypeHandler.areMatchingTypes(newType, oldType) && oldBoogieType.equals(newBoogieType)) {
			// types are already identical -- nothing to do
			return;
		}

		if (newType instanceof CPrimitive) {
			final CPrimitive cPrimitive = (CPrimitive) newType;
			if (cPrimitive.isIntegerType()) {
				convertToIntegerType(loc, rexp, (CPrimitive) newType);
			} else if (cPrimitive.isRealFloatingType()) {
				convertToFloatingType(loc, rexp, (CPrimitive) newType);
			} else if (cPrimitive.getType().equals(CPrimitives.VOID)) {
				convertToVoid(loc, rexp, (CPrimitive) newType);
			} else {
				throw new AssertionError("unknown type " + newType);
			}
		} else if (newType instanceof CPointer) {
			convertToPointer(loc, rexp, (CPointer) newType);
		} else if (newType instanceof CEnum) {
			// C standard 6.4.4.3.2
			// An identifier declared as an enumeration constant has type int.
			convertToIntegerType(loc, rexp, new CPrimitive(CPrimitives.INT));
		} else if (newType instanceof CArray) {
			throw new AssertionError("cannot convert to CArray");
		} else if (newType instanceof CFunction) {
			throw new AssertionError("cannot convert to CFunction");
		} else if (newType instanceof CStruct) {
			throw new UnsupportedSyntaxException(loc, "conversion to CStruct not implemented.");
		} else {
			throw new AssertionError("unknown type " + newType);
		}
	}

	/**
	 * Like {@link CHandler#doPointerArithmetic(int, ILocation, Expression, RValue, CType)} but additionally the integer
	 * operand is converted to the same type that we use to represent pointer components. As a consequence we have to
	 * return an ExpressionResult.
	 */
	public ExpressionResult doPointerArithmeticWithConversion(final Dispatcher main, final int operator,
			final ILocation loc, final Expression ptrAddress, final RValue integer, final CType valueType,
			final IASTNode hook) {
		final ExpressionResult eres = new ExpressionResult(integer);
		final ExpressionTranslation exprTrans = ((CHandler) main.mCHandler).getExpressionTranslation();
		exprTrans.convertIntToInt(loc, eres, exprTrans.getCTypeOfPointerComponents());
		final Expression resultExpression =
				mMemoryHandler.doPointerArithmetic(operator, loc, ptrAddress, (RValue) eres.mLrVal, valueType, hook);
		eres.mLrVal = new RValue(resultExpression, mExpressionTranslation.getCTypeOfPointerComponents());
		return eres;
	}

	@Override
	public ExpressionTranslation getExpressionTranslation() {
		return mExpressionTranslation;
	}

	@Override
	public FunctionHandler getFunctionHandler() {
		return mFunctionHandler;
	}

	@Override
	public InitializationHandler getInitHandler() {
		return mInitHandler;
	}

	@Override
	public MemoryHandler getMemoryHandler() {
		return mMemoryHandler;
	}

	@Override
	public StructHandler getStructHandler() {
		return mStructHandler;
	}

	@Override
	public StaticObjectsHandler getStaticObjectsHandler() {
		return mStaticObjectsHandler;
	}

	@Override
	public FlatSymbolTable getSymbolTable() {
		return mSymbolTable;
	}

	@Override
	public TypeSizeAndOffsetComputer getTypeSizeAndOffsetComputer() {
		return mTypeSizeComputer;
	}

	@Override
	public UnsignedTreatment getUnsignedTreatment() {
		return mUnsignedTreatment;
	}

	public Result handleLabelCommonCode(final Dispatcher main, final IASTLabelStatement node, final ILocation loc) {

		final ArrayList<Statement> stmt = new ArrayList<>();
		final ArrayList<Declaration> decl = new ArrayList<>();
		final List<Overapprox> overappr = new ArrayList<>();
		final String label = node.getName().toString();
		stmt.add(new Label(loc, label));
		final Result r = main.dispatch(node.getNestedStatement());
		if (r instanceof ExpressionResult) {
			final ExpressionResult res = (ExpressionResult) r;
			decl.addAll(res.mDecl);
			stmt.addAll(res.mStmt);
			overappr.addAll(res.mOverappr);
			return new ExpressionResult(stmt, res.mLrVal, decl, Collections.emptySet(), overappr);
		} else if (r instanceof SkipResult) {
			return new ExpressionResult(stmt, null, decl, Collections.emptySet(), overappr);
		} else { // r instanceof Result ...
			RValue expr = null;
			if (r.node instanceof Statement) {
				stmt.add((Statement) r.node);
			} else if (r.node instanceof Declaration) {
				decl.add((Declaration) r.node);
			} else if (r.node instanceof Expression) {
				expr = new RValue((Expression) r.node, null); // FIXME ??
			} else if (r.node instanceof Body) {
				// we already have a unique naming for variables! --> unfold
				final Body b = (Body) r.node;
				decl.addAll(Arrays.asList(b.getLocalVars()));
				stmt.addAll(Arrays.asList(b.getBlock()));
			} else {
				final String msg = "Unexpected boogie AST node type: " + r.node.getClass();
				throw new UnsupportedSyntaxException(loc, msg);
			}
			return new ExpressionResult(stmt, expr, decl, Collections.emptySet(), overappr);
		}
	}

	@Override
	public boolean isHeapVar(final String boogieId) {
		return mBoogieIdsOfHeapVars.contains(boogieId);
	}

	/**
	 *
	 * @param main
	 * @param loc
	 * @param leftHandSide
	 *            value of the left hand side that will be assigned to
	 * @param leftHandSideOtherUnionFields
	 *            information about union fields that need to be havocced in our struct representation of an off-heap
	 *            union
	 * @param rightHandSide
	 *            contains:
	 *            <li>the value (LRValue) of the right hand side of the assignment
	 *            <li>side effects (statements, declarations) etc. that are needed to prepare the value of the right
	 *            hand side of the assignment
	 *            <li>side effects that are needed to prepare the value of the left hand side of the assignment
	 * @return
	 */
	public ExpressionResult makeAssignment(final Dispatcher main, final ILocation loc, final LRValue leftHandSide,
			final List<ExpressionResult> leftHandSideOtherUnionFields, final ExpressionResult rightHandSide,
			final IASTNode hook) {

		// do implicit cast -- assume the types are compatible
		convert(loc, rightHandSide, leftHandSide.getCType());
		final RValue rightHandSideValueWithConversionsApplied = (RValue) rightHandSide.mLrVal;

		// for wraparound --> and avoiding it for ints that store pointers
		// updates the value in the symbol table accordingly
		// TODO: this is really ugly, do we still need this??
		if (rightHandSideValueWithConversionsApplied.isIntFromPointer()) {
			if (leftHandSide instanceof HeapLValue) {
				final Expression address = ((HeapLValue) leftHandSide).getAddress();
				if (address instanceof IdentifierExpression) {
					final String lId =
							((IdentifierExpression) ((HeapLValue) leftHandSide).getAddress()).getIdentifier();
					markAsIntFromPointer(loc, lId, hook);
				} else {
					// TODO
				}
			} else if (leftHandSide instanceof LocalLValue) {
				String lId = null;
				final LeftHandSide value = ((LocalLValue) leftHandSide).getLHS();
				if (value instanceof VariableLHS) {
					lId = ((VariableLHS) value).getIdentifier();
					markAsIntFromPointer(loc, lId, hook);
				} else {
					// TODO
				}
			}
			throw new AssertionError("Presumed that IntFromPointer workaound is not used any more.");
		}

		// add the assignment statement
		if (leftHandSide instanceof HeapLValue) {
			/*
			 * left hand side of assignment is on heap
			 */

			final ExpressionResultBuilder builder = new ExpressionResultBuilder();
			builder.addAllExceptLrValue(rightHandSide);

			/*
			 * construct and add a statement that
			 */
			final HeapLValue hlv = (HeapLValue) leftHandSide;

			Expression rhsWithBitfieldTreatment;
			if (hlv.getBitfieldInformation() != null) {
				final int bitfieldWidth = hlv.getBitfieldInformation().getNumberOfBits();
				rhsWithBitfieldTreatment =
						mExpressionTranslation.eraseBits(loc, rightHandSideValueWithConversionsApplied.getValue(),
								(CPrimitive) hlv.getCType().getUnderlyingType(), bitfieldWidth, hook);
			} else {
				rhsWithBitfieldTreatment = rightHandSideValueWithConversionsApplied.getValue();
			}
			builder.addStatements(mMemoryHandler.getWriteCall(main, loc, hlv, rhsWithBitfieldTreatment,
					rightHandSideValueWithConversionsApplied.getCType(), false, hook));

			/*
			 * the value of an assignment statement expression is the right hand side of the assignment
			 */
			builder.setLrVal(rightHandSideValueWithConversionsApplied);

			return builder.build();
		} else if (leftHandSide instanceof LocalLValue) {
			/*
			 * left hand side of assignment is off heap
			 */

			final ExpressionResultBuilder builder = new ExpressionResultBuilder();
			/*
			 * take over everything but neighbour union fields -- those will be given to assignorHavocUnionNeighbours as
			 * an extra parameter
			 */
			builder.addStatements(rightHandSide.getStatements());
			builder.addDeclarations(rightHandSide.getDeclarations());
			builder.addOverapprox(rightHandSide.getOverapprs());
			builder.addAuxVars(rightHandSide.getAuxVars());

			final LocalLValue lValue = (LocalLValue) leftHandSide;
			builder.setLrVal(lValue);

			Expression rhsWithBitfieldTreatment;
			if (lValue.getBitfieldInformation() != null) {
				final int bitfieldWidth = lValue.getBitfieldInformation().getNumberOfBits();
				rhsWithBitfieldTreatment =
						mExpressionTranslation.eraseBits(loc, rightHandSideValueWithConversionsApplied.getValue(),
								(CPrimitive) lValue.getCType(), bitfieldWidth, hook);
			} else {
				rhsWithBitfieldTreatment = rightHandSideValueWithConversionsApplied.getValue();
			}
			final AssignmentStatement assignStmt = StatementFactory.constructAssignmentStatement(loc,
					new LeftHandSide[] { lValue.getLHS() }, new Expression[] { rhsWithBitfieldTreatment });

			builder.addStatement(assignStmt);

			for (final Overapprox oa : rightHandSide.getOverapprs()) {
				for (final Statement stm : builder.getStatements()) {
					oa.annotate(stm);
				}
			}

			final ExpressionResultBuilder builderWithUnionFieldAndNeighboursUpdated = assignorHavocUnionNeighbours(main,
					loc, (RValue) rightHandSide.getLrValue(), rightHandSide.getNeighbourUnionFields(),
					rightHandSideValueWithConversionsApplied, builder, hook);

			// the following block's functionality has moved to FunctionHandler.constructAssignmentStatement(..)
			// if (!mFunctionHandler.isGlobalScope()) {
			//
			// final VariableLHS modifiedGlobal = new BoogieGlobalLhsFinder().getGlobalId(lValue.getLHS());
			// if (modifiedGlobal != null) {
			// mFunctionHandler.addModifiedGlobal(modifiedGlobal);
			// }
			// }
			return builderWithUnionFieldAndNeighboursUpdated.build();
		} else {
			throw new AssertionError("Type error: trying to assign to an RValue in Statement" + loc.toString());
		}
	}

	/**
	 * At the end of a scope, typically a C compound statement, we need to insert some mallocs and frees surrounding the
	 * stmt block, and we need to insert all the declarations that are needed for that block, according to the symbol
	 * table. (at the dispatch of a simple declaration, the declarations are stored in the symbol table)
	 *
	 * Updates the given ExpressionResultBuilder in place. Adds some declarations and resets the statements. Based on
	 * information in the symbol table concerning the scope that is to be closed.
	 */
	// public ArrayList<Statement> updateStmtsAndDeclsAtScopeEnd(final Dispatcher
	// main,
	public void updateStmtsAndDeclsAtScopeEnd(final Dispatcher main, final ExpressionResultBuilder exprResultBuilder,
			final IASTNode hook) {
		// final ArrayList<Declaration> decl,
		// ArrayList<Statement> stmt) {

		// stmt = mMemoryHandler.insertMallocs(main, stmt);

		exprResultBuilder.resetStatements(mMemoryHandler.insertMallocs(main, exprResultBuilder.getStatements(), hook));

		for (final SymbolTableValue stv : mSymbolTable.getInnermostCScopeValues(hook)) {
			// there may be a null declaration in case of foo(void) -- therefore we need to
			// check the second conjunct
			// (case where this is called from FunctionHandler.handleFunctionDefinition)
			if (!stv.isBoogieGlobalVar() && stv.getBoogieDecl() != null) {
				// decl.add(stv.getBoogieDecl());
				exprResultBuilder.addDeclaration(stv.getBoogieDecl());
			}
		}
		// return stmt;
	}

	/**
	 * Check if two pointers have the same base component (i.e. if both point to the same array object). Depending on
	 * the preferences of this plugin we
	 * <ul>
	 * <li>assert that both have the same base component,
	 * <li>assume that both have the same base component, or
	 * <li>add nothing.
	 * </ul>
	 *
	 * @param leftPtr
	 *            Boogie {@link Expression} that represents the left pointer.
	 * @param rightPtr
	 *            Boogie {@link Expression} that represents the right pointer.
	 * @param result
	 *            {@link ExpressionResult} to which the additional statements are added.
	 */
	private void addBaseEqualityCheck(final Dispatcher main, final ILocation loc, final Expression leftPtr,
			final Expression rightPtr, final ExpressionResult result) {
		if (mMemoryHandler.getPointerSubtractionAndComparisonValidityCheckMode() == PointerCheckMode.IGNORE) {
			// do not check anything
			return;
		}
		final Expression baseEquality = constructPointerComponentRelation(loc, IASTBinaryExpression.op_equals, leftPtr,
				rightPtr, SFO.POINTER_BASE);
		switch (mMemoryHandler.getPointerSubtractionAndComparisonValidityCheckMode()) {
		case ASSERTandASSUME:
			final Statement assertStm = new AssertStatement(loc, baseEquality);
			final Check chk = new Check(Spec.ILLEGAL_POINTER_ARITHMETIC);
			chk.annotate(assertStm);
			result.mStmt.add(assertStm);
			break;
		case ASSUME:
			final Statement assumeStm = new AssumeStatement(loc, baseEquality);
			result.mStmt.add(assumeStm);
			break;
		case IGNORE:
			throw new AssertionError("case handled before");
		default:
			throw new AssertionError("unknown value");
		}
	}

	/**
	 * Add to divisorExpRes a check if divisior is zero.
	 */
	private void addDivisionByZeroCheck(final Dispatcher main, final ILocation loc,
			final ExpressionResult divisorExpRes) {
		final Expression divisor = divisorExpRes.mLrVal.getValue();
		final CPrimitive divisorType = (CPrimitive) divisorExpRes.mLrVal.getCType();

		final PointerCheckMode checkMode;
		if (divisorType.isIntegerType()) {
			checkMode = main.getTranslationSettings().getDivisionByZeroOfIntegerTypes();
		} else if (divisorType.isFloatingType()) {
			checkMode = main.getTranslationSettings().getDivisionByZeroOfFloatingTypes();
		} else {
			throw new UnsupportedOperationException("cannot check division by zero for type " + divisorType);
		}

		if (checkMode == PointerCheckMode.IGNORE) {
			return;
		}

		final Expression divisorNotZero;
		if (divisorType.isIntegerType()) {
			final Expression zero =
					mExpressionTranslation.constructLiteralForIntegerType(loc, divisorType, BigInteger.ZERO);
			divisorNotZero = mExpressionTranslation.constructBinaryEqualityExpression(loc,
					IASTBinaryExpression.op_notequals, divisor, divisorType, zero, divisorType);
		} else if (divisorType.isFloatingType()) {
			final Expression zero =
					mExpressionTranslation.constructLiteralForFloatingType(loc, divisorType, BigDecimal.ZERO);
			divisorNotZero = mExpressionTranslation.constructBinaryComparisonFloatingPointExpression(loc,
					IASTBinaryExpression.op_notequals, divisor, divisorType, zero, divisorType);
		} else {
			throw new UnsupportedOperationException("cannot check division by zero for type " + divisorType);
		}

		final Statement additionalStatement;
		if (checkMode == PointerCheckMode.ASSUME) {
			additionalStatement = new AssumeStatement(loc, divisorNotZero);
		} else if (checkMode == PointerCheckMode.ASSERTandASSUME) {
			additionalStatement = new AssertStatement(loc, divisorNotZero);
			final Check check = new Check(Check.Spec.DIVISION_BY_ZERO);
			check.annotate(additionalStatement);
		} else {
			throw new AssertionError("illegal");
		}
		divisorExpRes.mStmt.add(additionalStatement);
	}

	/**
	 * Add checks for integer overflows. Construct arithmetic operation and add an assert statement that checks if the
	 * result is in the range of the corresponding C data type (i.e. check for overflow wrt. max and min value). Note
	 * that we do not check if a given expression is in the range. We explicitly construct a new expression for the
	 * arithmetic operation in this check because we possibly have to adjust the data type used in boogie. E.g., if we
	 * use 32bit bitvectors in Boogie we are unable to express an overflow check for a 32bit integer addition in C.
	 * Instead, we have to use a 33bit bit bitvector in Boogie.
	 */
	private void addIntegerBoundsCheck(final Dispatcher main, final ILocation loc, final ExpressionResult rex,
			final CPrimitive resultType, final int operation, final IASTNode hook, final Expression... operands) {
		if (main.getPreferences().getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_SIGNED_INTEGER_BOUNDS)
				&& resultType.isIntegerType() && !main.getTypeSizes().isUnsigned(resultType)) {
			final Check check = new Check(Spec.INTEGER_OVERFLOW);
			final Expression operationResult;
			if (operation == IASTBinaryExpression.op_shiftLeft
					|| operation == IASTBinaryExpression.op_shiftLeftAssign) {
				// 2017-11-18 Matthias: For this shift there are more possibilities of undefined
				// behavior
				// I don't know where we should check them and if we should call them
				// "signed integer overflows" (probably not)
				operationResult = mExpressionTranslation.constructBinaryBitwiseIntegerExpression(loc, operation,
						operands[0], resultType, operands[1], resultType, hook);
			} else if (operands.length == 1) {
				operationResult =
						mExpressionTranslation.constructUnaryExpression(loc, operation, operands[0], resultType);
			} else if (operands.length == 2) {
				operationResult = mExpressionTranslation.constructArithmeticExpression(loc, operation, operands[0],
						resultType, operands[1], resultType);
			} else {
				throw new AssertionError("no such operation");
			}
			{
				final Expression smallerMaxInt = ExpressionFactory.newBinaryExpression(loc,
						BinaryExpression.Operator.COMPLEQ, operationResult, ExpressionFactory.createIntegerLiteral(loc,
								main.getTypeSizes().getMaxValueOfPrimitiveType(resultType).toString()));
				if (!ExpressionFactory.isTrueLiteral(smallerMaxInt)) {
					final AssertStatement smallerMaxIntStmt = new AssertStatement(loc, smallerMaxInt);
					check.annotate(smallerMaxIntStmt);
					rex.mStmt.add(smallerMaxIntStmt);
				}
			}
			{
				final Expression biggerMinInt = ExpressionFactory.newBinaryExpression(loc,
						BinaryExpression.Operator.COMPGEQ, operationResult, ExpressionFactory.createIntegerLiteral(loc,
								main.getTypeSizes().getMinValueOfPrimitiveType(resultType).toString()));
				if (!ExpressionFactory.isTrueLiteral(biggerMinInt)) {
					final AssertStatement biggerMinIntStmt = new AssertStatement(loc, biggerMinInt);
					check.annotate(biggerMinIntStmt);
					rex.mStmt.add(biggerMinIntStmt);
				}
			}
		}
	}

	/**
	 * Check if pointer offset is in a legal range. In case a pointer points to allocated memory, the "base" of a
	 * pointer points to some array object (in C). Now we check if the offset of this pointer does not violate the
	 * bounds of that array. This means that the offset
	 * <ul>
	 * <li>must be non-negative, and
	 * <li>must be small enough that the pointer points to an element of the array or one past the last element of the
	 * array.
	 * </ul>
	 * Depending on the preferences of this plugin we
	 * <ul>
	 * <li>assert that the offset is in the bounds of the array,
	 * <li>assume that the offset is in the bounds of the array, or
	 * <li>add nothing.
	 * </ul>
	 *
	 * @param ptr
	 *            Boogie {@link Expression} that represents the pointer.
	 * @param result
	 *            {@link ExpressionResult} to which the additional statements are added.
	 */
	private void addOffsetInBoundsCheck(final Dispatcher main, final ILocation loc, final Expression ptr,
			final ExpressionResult result) {
		// TODO: Matthias 2015-09-08 implement this
		// maybe additional parameters are required.
	}

	/**
	 * add havocs if we have a write to a union (which is not on heap, otherwise the heap model should deal with
	 * everything)
	 *
	 * @param loc
	 * @param rVal
	 * @param neighbourUnionFields
	 * @param rightHandSideWithConversionsApplied
	 * @param builder
	 * @return
	 */
	private ExpressionResultBuilder assignorHavocUnionNeighbours(final Dispatcher main, final ILocation loc,
			final RValue rVal, final Collection<ExpressionResult> neighbourUnionFields,
			final RValue rightHandSideWithConversionsApplied, final ExpressionResultBuilder builderIn,
			final IASTNode hook) {
		ExpressionResultBuilder builder = new ExpressionResultBuilder(builderIn);

		for (final ExpressionResult er : neighbourUnionFields) {
			// do not havoc when the type of the field is "compatible"
			if (rightHandSideWithConversionsApplied.getCType().equals(er.mLrVal.getCType())
					|| rightHandSideWithConversionsApplied.getCType().getUnderlyingType() instanceof CPrimitive
							&& er.mLrVal.getCType() instanceof CPrimitive
							&& ((CPrimitive) rightHandSideWithConversionsApplied.getCType().getUnderlyingType())
									.getGeneralType().equals(((CPrimitive) er.mLrVal.getCType()).getGeneralType())
							&& mMemoryHandler.calculateSizeOf(loc, rightHandSideWithConversionsApplied.getCType(),
									hook) == mMemoryHandler.calculateSizeOf(loc, er.mLrVal.getCType(), hook)) {

				// builder = new ExpressionResultBuilder(makeAssignment(main, loc,
				// builder.mStatements, er.mLrVal, rVal,
				// builder.mDeclarations, builder.mAuxVars, builder.mOverappr));
				// builder.setLrVal(rVal);
				builder.resetLrVal(rVal);
				final ExpressionResult assignment =
						makeAssignment(main, loc, er.mLrVal, Collections.emptyList(), builder.build(), hook);
				builder =
						new ExpressionResultBuilder().addAllExceptLrValue(assignment).setLrVal(assignment.getLrValue());
				// rVal,
				// builder.mDeclarations, builder.mAuxVars, builder.mOverappr));

			} else {
				// otherwise we consider the value undefined, thus havoc it
				// TODO: maybe not use auxiliary variables so lavishly
				// final String tmpId = mNameHandler.getTempVarUID(SFO.AUXVAR.UNION,
				// er.mLrVal.getCType());
				// final VariableDeclaration tVarDec =
				// new VariableDeclaration(loc, new Attribute[0], new VarList[] { new
				// VarList(loc,
				// new String[] { tmpId }, mTypeHandler.cType2AstType(loc,
				// er.mLrVal.getCType())) });
				final AuxVarInfo auxVar =
						AuxVarInfo.constructAuxVarInfo(loc, main, er.mLrVal.getCType(), SFO.AUXVAR.UNION);

				// builder.addDeclaration(tVarDec).putAuxVar(tVarDec, loc);
				builder.addDeclaration(auxVar.getVarDec());
				// builder.putAuxVar(auxVar.getVarDec(), loc);
				builder.addAuxVar(auxVar);

				// final Expression tmpVarIdExpr = new IdentifierExpression(loc, tmpId);
				final RValue tmpVarRVal = new RValueForArrays(auxVar.getExp(), er.mLrVal.getCType());

				// builder.addOverapprox(new Overapprox("union field of non-heap union updated "
				// + "--> havoccing other fields (CHandler.makeAssignment(..))", loc));

				final Overapprox overapp = new Overapprox(
						"field of union updated " + "--> havoccing other fields (CHandler.makeAssignment(..))", loc);
				builder.addOverapprox(overapp);

				builder.resetLrVal(tmpVarRVal);

				final ExpressionResult assignment =
						makeAssignment(main, loc, er.mLrVal, Collections.emptyList(), builder.build(), hook);

				// builder = new ExpressionResultBuilder(makeAssignment(main, loc,
				// builder.mStatements, er.mLrVal,
				// tmpVarRVal, builder.mDeclarations, builder.mAuxVars,
				// Collections.singletonList(overapp)));
				builder =
						new ExpressionResultBuilder().addAllExceptLrValue(assignment).setLrVal(assignment.getLrValue());
			}
		}
		return builder;
	}

	/**
	 * Checks ACSL for the next element and whether it must be added at the place where this method is called.
	 *
	 * @param main
	 *            the main dispatcher.
	 * @param stmt
	 *            the statement list where the acsl should be appended - this is assumed to be <code>null</code> when
	 *            called from within the <i>translation unit</i>.
	 * @param next
	 *            the current child node of a translation unit of compound statement that will be added next. Should be
	 *            <code>null</code> when called at the end of <i>compound statement</i>.
	 * @param resultBuilder
	 *            the result builder where code translated from the ACSL code can be added to by this method
	 * @param compoundStatement
	 *            true iff this method was called during translation of a compound statement
	 * @param translationUnit
	 *            true iff this method was called during translation of the translation unit
	 * @param parent
	 *            the parent node of the current ACSL node. This should only be set if called at the end of a
	 *            <i>compound statement</i> and <code>null</code> otherwise.
	 */
	private void checkForACSL(final Dispatcher main, final ExpressionResultBuilder resultBuilder, // final
																									// List<Statement>
																									// stmt, final
																									// List<Declaration>
																									// decl,
			final IASTNode next, final IASTNode parent, final boolean compoundStatement) {
		if (mAcsl != null) {
			if (next instanceof IASTTranslationUnit) {
				for (final ACSLNode globAcsl : mAcsl.getAcsl()) {
					if (globAcsl instanceof GlobalLTLInvariant) {
						final LTLExpressionExtractor extractor = new LTLExpressionExtractor();
						extractor.run(globAcsl);
						mGlobAcslExtractors.add(extractor);
						try {
							mAcsl = main.nextACSLStatement();
						} catch (final ParseException e1) {
							final String msg = "Skipped a ACSL node due to: " + e1.getMessage();
							final ILocation loc = main.getLocationFactory().createCLocation(parent);
							main.unsupportedSyntax(loc, msg);
						}
					}
				} // TODO: deal with other global ACSL stuff
			} else if (mAcsl.getSuccessorCNode() == null) {
				// if (parent != null && stmt != null && next == null) {
				// TODO: unclear what the stmt != null case should be
				if (parent != null && compoundStatement && next == null) {
					// ACSL at the end of a function or at the end of the last statement in a switch
					// that is not
					// terminated by a break
					// TODO: the latter case needs fixing, the ACSL is inserted outside the
					// corresponding if-scope right
					// now
					// example: int s = 1; switch (s) { case 0: s++; //@ assert \false; } will yield
					// a unsafe boogie
					// program
					for (final ACSLNode acslNode : mAcsl.getAcsl()) {
						if (parent.getFileLocation().getEndingLineNumber() <= acslNode.getStartingLineNumber()) {
							return;// handle later ...
						} else if (parent.getFileLocation().getEndingLineNumber() >= acslNode.getEndingLineNumber()
								&& parent.getFileLocation().getStartingLineNumber() <= acslNode
										.getStartingLineNumber()) {
							final Result acslResult = main.dispatch(acslNode, parent);
							if (acslResult instanceof ExpressionResult) {
								resultBuilder.addDeclarations(((ExpressionResult) acslResult).mDecl);
								resultBuilder.addStatements(((ExpressionResult) acslResult).mStmt);
								resultBuilder.addStatements(CTranslationUtil
										.createHavocsForAuxVars(((ExpressionResult) acslResult).mAuxVars));
								try {
									mAcsl = main.nextACSLStatement();
								} catch (final ParseException e1) {
									final String msg = "Skipped a ACSL node due to: " + e1.getMessage();
									final ILocation loc = main.getLocationFactory().createCLocation(parent);
									main.unsupportedSyntax(loc, msg);
								}
							} else {
								final String msg = "Unexpected ACSL comment: " + acslResult.node.getClass();
								final ILocation loc = main.getLocationFactory().createCLocation(parent);
								throw new IncorrectSyntaxException(loc, msg);
							}
						}
					}
				}

				// ELSE:
				// ACSL for next compound statement -> handle it next call
				// or in case of translation unit, ACSL in an unexpected
				// location!
			} else if (mAcsl.getSuccessorCNode().equals(next)) {
				assert mContract.isEmpty();
				for (final ACSLNode acslNode : mAcsl.getAcsl()) {
					// if (stmt != null) {
					if (compoundStatement) {
						// this means we are in a compound statement
						if (acslNode instanceof Contract || acslNode instanceof LoopAnnot) {
							// Loop contract
							mContract.add(acslNode);
						} else if (acslNode instanceof CodeAnnot) {
							final Result acslResult = main.dispatch(acslNode, next == null ? parent : next);
							if (acslResult instanceof ExpressionResult) {
								final ExpressionResult re = (ExpressionResult) acslResult;
								resultBuilder.addStatements(re.mStmt);
								resultBuilder.addDeclarations(re.mDecl);
							} else {
								resultBuilder.addStatement((Statement) acslResult.node);
							}
						} else {
							final String msg = "Unexpected ACSL comment: " + acslNode.getClass();
							final ILocation loc = main.getLocationFactory().createCLocation(next);
							throw new IncorrectSyntaxException(loc, msg);
						}
					} else {
						// } else if (translationUnit) {
						// this means we are in the translation unit
						if (acslNode instanceof Contract || acslNode instanceof LoopAnnot) {
							// Function contract
							mContract.add(acslNode);
						}
					}
				}
				try {
					mAcsl = main.nextACSLStatement();
				} catch (final ParseException e1) {
					final String msg = "Skipped a ACSL node due to: " + e1.getMessage();
					final ILocation loc = main.getLocationFactory().createCLocation(parent);
					main.unsupportedSyntax(loc, msg);
				}

			}
		}
	}

	/**
	 * Construct {@link Expression} that compares a component of two pointers.
	 *
	 * @param loc
	 * @param op
	 *            Comparison operation.
	 * @param leftPointer
	 *            Boogie expression that represents pointer.
	 * @param rightPointer
	 *            Boogie expression that represents pointer.
	 * @param component
	 *            Defines which component is compared. Either "base" or "offset"
	 */
	private Expression constructPointerComponentRelation(final ILocation loc, final int op,
			final Expression leftPointer, final Expression rightPointer, final String component) {
		assert component.equals(SFO.POINTER_BASE) || component.equals(SFO.POINTER_OFFSET) : "unknown pointer component";
		final StructAccessExpression leftComponent =
				ExpressionFactory.constructStructAccessExpression(loc, leftPointer, component);
		final StructAccessExpression rightComponent =
				ExpressionFactory.constructStructAccessExpression(loc, rightPointer, component);
		switch (op) {
		case IASTBinaryExpression.op_equals:
		case IASTBinaryExpression.op_notequals: {
			return mExpressionTranslation.constructBinaryEqualityExpression(loc, op, leftComponent,
					mExpressionTranslation.getCTypeOfPointerComponents(), rightComponent,
					mExpressionTranslation.getCTypeOfPointerComponents());
		}
		case IASTBinaryExpression.op_lessThan:
		case IASTBinaryExpression.op_lessEqual:
		case IASTBinaryExpression.op_greaterThan:
		case IASTBinaryExpression.op_greaterEqual:
			return mExpressionTranslation.constructBinaryComparisonExpression(loc, op, leftComponent,
					mExpressionTranslation.getCTypeOfPointerComponents(), rightComponent,
					mExpressionTranslation.getCTypeOfPointerComponents());
		default:
			throw new IllegalArgumentException("op " + op);
		}
	}

	/**
	 * Increment or decrement an expression. Construct expression that represents the value of the input expression but
	 * is incremented or decremented by one. If op is IASTBinaryExpression.op_plus we increment, if op is
	 * IASTBinaryExpression.op_minus we decrement. If ctype is CPrimitive, we increment/decrement by one and also call
	 * the method that adds (depending on the settings) an overflow check. If ctype is CPointer, we increment/decrement
	 * by the size of the pointsToType and call the method that adds (depending on the settings) an check if the pointer
	 * arithmetic was legal.
	 *
	 * @param result
	 *            note that this method has sideeffects on this object! (add..BoundCheck(..) calls)
	 */
	private Expression constructXcrementedValue(final Dispatcher main, final ILocation loc,
			final ExpressionResult result, final CType ctype, final int op, final Expression value,
			final IASTNode hook) {
		assert op == IASTBinaryExpression.op_plus
				|| op == IASTBinaryExpression.op_minus : "has to be either minus or plus";
		final Expression valueIncremented;
		if (ctype instanceof CPointer) {
			final CPointer cPointer = (CPointer) ctype;
			final Expression oneEpr = mExpressionTranslation.constructLiteralForIntegerType(loc,
					mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ONE);
			final CPrimitive oneType = mExpressionTranslation.getCTypeOfPointerComponents();
			final RValue one = new RValue(oneEpr, oneType);
			valueIncremented = mMemoryHandler.doPointerArithmetic(op, loc, value, one, cPointer.pointsToType, hook);
			addOffsetInBoundsCheck(main, loc, valueIncremented, result);
		} else if (ctype instanceof CPrimitive) {
			final CPrimitive cPrimitive = (CPrimitive) ctype;

			final Expression one;
			if (ctype.isFloatingType()) {
				one = mExpressionTranslation.constructLiteralForFloatingType(loc, cPrimitive, BigDecimal.ONE);
			} else {
				one = mExpressionTranslation.constructLiteralForIntegerType(loc, cPrimitive, BigInteger.ONE);
			}
			addIntegerBoundsCheck(main, loc, result, cPrimitive, op, hook, value, one);
			valueIncremented =
					mExpressionTranslation.constructArithmeticExpression(loc, op, value, cPrimitive, one, cPrimitive);
		} else {
			throw new IllegalArgumentException("input has to be CPointer or CPrimitive");
		}
		return valueIncremented;
	}

	private void convertToFloatingType(final ILocation loc, final ExpressionResult rexp, final CPrimitive newType) {
		assert rexp.mLrVal instanceof RValue : "has to be converted to RValue";
		final CType oldType = rexp.mLrVal.getCType().getUnderlyingType();
		if (oldType instanceof CPrimitive) {
			final CPrimitive cPrimitive = (CPrimitive) oldType;
			if (cPrimitive.isIntegerType()) {
				mExpressionTranslation.convertIntToFloat(loc, rexp, newType);
			} else if (cPrimitive.isRealFloatingType()) {
				mExpressionTranslation.convertFloatToFloat(loc, rexp, newType);
			} else if (cPrimitive.getType().equals(CPrimitives.VOID)) {
				throw new IncorrectSyntaxException(loc, "cannot convert from void");
			} else {
				throw new AssertionError("unknown type " + newType);
			}
		} else if (oldType instanceof CPointer) {
			throw new IncorrectSyntaxException(loc, "cannot convert pointer to float");
		} else if (oldType instanceof CEnum) {
			mExpressionTranslation.convertIntToFloat(loc, rexp, newType);
		} else if (oldType instanceof CArray) {
			throw new AssertionError("cannot convert from CArray");
		} else if (oldType instanceof CFunction) {
			throw new AssertionError("cannot convert from CFunction");
		} else if (oldType instanceof CStruct) {
			throw new UnsupportedSyntaxException(loc, "conversion from CStruct not implemented.");
		} else {
			throw new AssertionError("unknown type " + newType);
		}
	}

	private void convertToIntegerType(final ILocation loc, final ExpressionResult rexp, final CPrimitive newType) {
		assert rexp.mLrVal instanceof RValue : "has to be converted to RValue";
		final CType oldType = rexp.mLrVal.getCType().getUnderlyingType();
		if (oldType instanceof CPrimitive) {
			final CPrimitive cPrimitive = (CPrimitive) oldType;
			if (cPrimitive.isIntegerType()) {
				mExpressionTranslation.convertIntToInt(loc, rexp, newType);
			} else if (cPrimitive.isRealFloatingType()) {
				mExpressionTranslation.convertFloatToInt(loc, rexp, newType);
			} else if (cPrimitive.getType().equals(CPrimitives.VOID)) {
				throw new IncorrectSyntaxException(loc, "cannot convert from void");
			} else {
				throw new AssertionError("unknown type " + newType);
			}
		} else if (oldType instanceof CPointer) {
			mExpressionTranslation.convertPointerToInt(loc, rexp, newType);
		} else if (oldType instanceof CEnum) {
			mExpressionTranslation.convertIntToInt(loc, rexp, newType);
		} else if (oldType instanceof CArray) {
			throw new AssertionError("cannot convert from CArray");
		} else if (oldType instanceof CFunction) {
			throw new AssertionError("cannot convert from CFunction");
		} else if (oldType instanceof CStruct) {
			throw new UnsupportedSyntaxException(loc, "conversion from CStruct not implemented.");
		} else {
			throw new AssertionError("unknown type " + newType);
		}
	}

	private void convertToPointer(final ILocation loc, final ExpressionResult rexp, final CPointer newType) {
		assert rexp.mLrVal instanceof RValue : "has to be converted to RValue";
		final CType oldType = rexp.mLrVal.getCType().getUnderlyingType();
		if (oldType instanceof CPrimitive) {
			final CPrimitive cPrimitive = (CPrimitive) oldType;
			if (cPrimitive.isIntegerType()) {
				mExpressionTranslation.convertIntToPointer(loc, rexp, newType);
			} else if (cPrimitive.isRealFloatingType()) {
				throw new IncorrectSyntaxException(loc, "cannot convert float to pointer");
			} else if (cPrimitive.getType().equals(CPrimitives.VOID)) {
				throw new IncorrectSyntaxException(loc, "cannot convert from void");
			} else {
				throw new AssertionError("unknown type " + newType);
			}
		} else if (oldType instanceof CPointer) {
			convertPointerToPointer(loc, rexp, newType);
		} else if (oldType instanceof CEnum) {
			mExpressionTranslation.convertIntToPointer(loc, rexp, newType);
		} else if (oldType instanceof CArray) {
			if (rexp instanceof StringLiteralResult) {
				/*
				 * a string literal's char-array decays to a pointer the stringLiteralResult already has the correct
				 * RValue, we just need to change the type
				 */
				rexp.mLrVal = new RValue(rexp.mLrVal.getValue(), new CPointer(new CPrimitive(CPrimitives.CHAR)));
			} else {
				throw new AssertionError("cannot convert from CArray");
			}
		} else if (oldType instanceof CFunction) {
			throw new AssertionError("cannot convert from CFunction");
		} else if (oldType instanceof CStruct) {
			throw new UnsupportedSyntaxException(loc, "conversion from CStruct not implemented.");
		} else {
			throw new AssertionError("unknown type " + newType);
		}
	}

	/**
	 * Subtract two pointers.
	 *
	 * @param leftPtr
	 *            Boogie {@link Expression} that represents the left pointer.
	 * @param rightPtr
	 *            Boogie {@link Expression} that represents the right pointer.
	 * @param pointsToType
	 *            {@link CType} of the objects to which the pointers point.
	 * @return An {@link Expression} that represents the difference of two Pointers according to C11 6.5.6.9.
	 */
	private Expression doPointerSubtraction(final Dispatcher main, final ILocation loc, final Expression ptr1,
			final Expression ptr2, final CType pointsToType, final IASTNode hook) {
		final Expression ptr1Offset = ExpressionFactory.constructStructAccessExpression(loc, ptr1, SFO.POINTER_OFFSET);
		final Expression ptr2Offset = ExpressionFactory.constructStructAccessExpression(loc, ptr2, SFO.POINTER_OFFSET);
		final Expression offsetDifference = mExpressionTranslation.constructArithmeticExpression(loc,
				IASTBinaryExpression.op_minus, ptr1Offset, mExpressionTranslation.getCTypeOfPointerComponents(),
				ptr2Offset, mExpressionTranslation.getCTypeOfPointerComponents());
		final Expression typesize = mMemoryHandler.calculateSizeOf(loc, pointsToType, hook);
		final CPrimitive typesizeType = new CPrimitive(CPrimitives.INT);
		// TODO: typesizeType and .getCTypeOfPointerComponents() might be
		// different then one expression has to be converted into the type of
		// the other
		final Expression offsetDifferenceDividedByTypesize =
				mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_divide,
						offsetDifference, mExpressionTranslation.getCTypeOfPointerComponents(), typesize, typesizeType);
		return offsetDifferenceDividedByTypesize;
	}

	/**
	 * Handle the indirection operator according to Section 6.5.3.2 of C11. (The indirection operator is the star for
	 * pointer dereference.)
	 */
	private static Result handleIndirectionOperator(final Dispatcher main, final ExpressionResult er,
			final ILocation loc, final IASTNode hook) {
		final ExpressionResult rop = er.switchToRValueIfNecessary(main, loc, hook);
		final RValue rValue = (RValue) rop.mLrVal;
		if (!(rValue.getCType().getUnderlyingType() instanceof CPointer)) {
			throw new IllegalArgumentException("dereference needs pointer but got " + rValue.getCType());
		}
		final CPointer pointer = (CPointer) rValue.getCType().getUnderlyingType();
		final CType pointedType = pointer.pointsToType;
		if (pointedType.isIncomplete()) {
			throw new IncorrectSyntaxException(loc, "Pointer dereference of incomplete type");
		}

		return new ExpressionResult(rop.mStmt,
				LRValueFactory.constructHeapLValue(main, rValue.getValue(), pointedType, null), rop.mDecl, rop.mAuxVars,
				rop.mOverappr);
	}

	/**
	 * Method that handles loops (for, while, do/while). Each of corresponding visit methods will call this method.
	 *
	 * @param main
	 *            the main dispatcher
	 * @param node
	 *            the node to visit
	 * @param bodyResult
	 *            the body component of the corresponding loop
	 * @param condResult
	 *            the condition of the loop
	 * @param loopLabel
	 * @param witnessInvariant
	 * @return a result object holding the translated loop (i.e. a while loop)
	 */
	private Result handleLoops(final Dispatcher main, final IASTStatement node, Result bodyResult,
			ExpressionResult condResult, final String loopLabel, final LoopInvariantSpecification witnessInvariant) {
		assert node instanceof IASTWhileStatement || node instanceof IASTDoStatement
				|| node instanceof IASTForStatement;

		final ILocation loc = main.getLocationFactory().createCLocation(node);

		// final ArrayList<Statement> stmt = new ArrayList<>();
		// final ArrayList<Declaration> decl = new ArrayList<>();
		// final List<Overapprox> overappr = new ArrayList<>();
		// final Map<VariableDeclaration, ILocation> emptyAuxVars = new
		// LinkedHashMap<>(0);
		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();

		Result iterator = null;
		if (node instanceof IASTForStatement) {
			final IASTForStatement forStmt = (IASTForStatement) node;
			// add initialization for this for loop
			final IASTStatement cInitStmt = forStmt.getInitializerStatement();
			if (cInitStmt != null) {
				beginScope();
				final Result initializer = main.dispatch(cInitStmt);
				if (initializer instanceof ExpressionResult) {
					final ExpressionResult rExp = (ExpressionResult) initializer;
					// stmt.addAll(rExp.mStmt);
					// decl.addAll(rExp.mDecl);
					// overappr.addAll(rExp.mOverappr);
					resultBuilder.addAllExceptLrValue(rExp);
				} else if (initializer instanceof SkipResult) {
					// this is an empty statement in the C Code. We will skip it
				} else {
					final String msg = "Uninplemented type of for loop initialization: " + initializer.getClass();
					throw new UnsupportedSyntaxException(loc, msg);
				}
			}

			// translate iterator
			final IASTExpression cItExpr = forStmt.getIterationExpression();
			if (cItExpr != null) {
				iterator = main.dispatch(cItExpr);
			}

			// translate condition
			final IASTExpression cCondExpr = forStmt.getConditionExpression();
			if (cCondExpr != null) {
				condResult = (ExpressionResult) main.dispatch(cCondExpr);
			} else {
				condResult = new ExpressionResult(new RValue(ExpressionFactory.createBooleanLiteral(loc, true),
						new CPrimitive(CPrimitives.BOOL), true), Collections.emptySet());
			}

			mInnerMostLoopLabel.push(loopLabel);
			bodyResult = main.dispatch(forStmt.getBody());
			mInnerMostLoopLabel.pop();
		}
		assert CTranslationUtil.isAuxVarMapComplete(mNameHandler, condResult.mDecl, condResult.mAuxVars);

		List<Statement> bodyBlock = new ArrayList<>();
		if (bodyResult instanceof ExpressionResult) {
			final ExpressionResult re = (ExpressionResult) bodyResult;
			// decl.addAll(re.mDecl);
			// overappr.addAll(re.mOverappr);
			resultBuilder.addDeclarations(re.getDeclarations());
			resultBuilder.addOverapprox(re.getOverapprs());
			bodyBlock.addAll(re.mStmt);
		} else if (bodyResult != null) {
			if (bodyResult.node instanceof Body) {
				final Body body = (Body) bodyResult.node;
				bodyBlock.addAll(Arrays.asList(body.getBlock()));
				// decl.addAll(Arrays.asList(body.getLocalVars()));
				resultBuilder.addDeclarations(Arrays.asList(body.getLocalVars()));
			} else if (bodyResult instanceof SkipResult) {
				// do nothing - this is the special case where the loop does
				// not have a body.
			} else {
				final String msg = "Error: unexpected dispatch result" + bodyResult.getClass();
				throw new UnsupportedSyntaxException(loc, msg);
			}
		}

		if (node instanceof IASTForStatement) {
			// add the loop label (continue statements become a jump to the loop label)
			bodyBlock.add(new Label(loc, loopLabel));
		}

		if (node instanceof IASTForStatement && iterator != null) {
			// add iterator statements of this for loop
			if (iterator instanceof ExpressionListResult) {
				for (final ExpressionResult el : ((ExpressionListResult) iterator).list) {
					bodyBlock.addAll(el.mStmt);
					// decl.addAll(el.mDecl);
					resultBuilder.addDeclarations(el.getDeclarations());
					bodyBlock.addAll(CTranslationUtil.createHavocsForAuxVars(el.mAuxVars));
				}
			} else if (iterator instanceof ExpressionResult) {
				final ExpressionResult iteratorRE = (ExpressionResult) iterator;
				bodyBlock.addAll(iteratorRE.mStmt);
				// decl.addAll(iteratorRE.mDecl);
				// overappr.addAll(iteratorRE.mOverappr);
				resultBuilder.addDeclarations(iteratorRE.getDeclarations());
				resultBuilder.addOverapprox(iteratorRE.getOverapprs());
				bodyBlock.addAll(CTranslationUtil.createHavocsForAuxVars(iteratorRE.mAuxVars));
			} else {
				final String msg = "Uninplemented type of loop iterator: " + iterator.getClass();
				throw new UnsupportedSyntaxException(loc, msg);
			}
		}

		condResult = condResult.switchToRValueIfNecessary(main, loc, node);
		condResult.rexIntToBoolIfNecessary(loc, mExpressionTranslation, mMemoryHandler);
		// decl.addAll(condResult.mDecl);
		resultBuilder.addDeclarations(condResult.getDeclarations());
		final RValue condRVal = (RValue) condResult.mLrVal;
		IfStatement ifStmt;
		{
			final Expression cond = ExpressionFactory.constructUnaryExpression(loc, UnaryExpression.Operator.LOGICNEG,
					condRVal.getValue());
			final ArrayList<Statement> thenStmt =
					new ArrayList<>(CTranslationUtil.createHavocsForAuxVars(condResult.getAuxVars()));
			thenStmt.add(new BreakStatement(loc));
			final Statement[] elseStmt =
					CTranslationUtil.createHavocsForAuxVars(condResult.getAuxVars()).toArray(new Statement[0]);
			ifStmt = new IfStatement(loc, cond, thenStmt.toArray(new Statement[thenStmt.size()]), elseStmt);
		}

		if (node instanceof IASTWhileStatement || node instanceof IASTForStatement) {
			bodyBlock.add(0, ifStmt);
			bodyBlock.addAll(0, condResult.mStmt);
			if (node instanceof IASTWhileStatement) {
				bodyBlock.add(0, new Label(loc, loopLabel));
			}
		} else if (node instanceof IASTDoStatement) {
			bodyBlock.add(new Label(loc, loopLabel));
			bodyBlock.addAll(condResult.mStmt);
			bodyBlock.add(ifStmt);
		}

		LoopInvariantSpecification[] spec;
		if (mContract == null) {
			spec = new LoopInvariantSpecification[0];
		} else {
			final List<LoopInvariantSpecification> specList = new ArrayList<>();
			if (witnessInvariant != null) {
				specList.add(witnessInvariant);
			}
			if (node instanceof IASTForStatement) {
				for (int i = 0; i < mContract.size(); i++) {
					// retranslate ACSL specification needed e.g., in cases
					// where ids of function parameters differ from is in ACSL
					// expression
					final Result retranslateRes = main.dispatch(mContract.get(i), node);
					if (retranslateRes instanceof ContractResult) {
						final ContractResult resContr = (ContractResult) retranslateRes;
						assert resContr.specs.length == 1;
						for (final Specification cSpec : resContr.specs) {
							specList.add((LoopInvariantSpecification) cSpec);
						}
					} else {
						specList.add((LoopInvariantSpecification) retranslateRes.node);
					}
				}
			}
			spec = specList.toArray(new LoopInvariantSpecification[specList.size()]);
			clearContract(); // take care for behavior and completeness
		}

		// bit of a workaround using an extra builder here..
		final ExpressionResultBuilder bodyBlockResultBuilder = new ExpressionResultBuilder();
		bodyBlockResultBuilder.addStatements(bodyBlock);

		if (node instanceof IASTForStatement) {
			if (((IASTForStatement) node).getInitializerStatement() != null) {
				// bodyBlock = updateStmtsAndDeclsAtScopeEnd(main, decl, bodyBlock);
				updateStmtsAndDeclsAtScopeEnd(main, bodyBlockResultBuilder, node);
				endScope();

				resultBuilder.addDeclarations(bodyBlockResultBuilder.getDeclarations());
				bodyBlock = bodyBlockResultBuilder.getStatements();
			}
		}

		final ILocation ignoreLocation = LocationFactory.createIgnoreCLocation(node);
		final WhileStatement whileStmt =
				new WhileStatement(ignoreLocation, ExpressionFactory.createBooleanLiteral(ignoreLocation, true), spec,
						bodyBlock.toArray(new Statement[bodyBlock.size()]));
		// overappr.stream().forEach(a -> a.annotate(whileStmt));
		// stmt.add(whileStmt);
		resultBuilder.getOverappr().stream().forEach(a -> a.annotate(whileStmt));
		resultBuilder.addStatement(whileStmt);

		// return new ExpressionResult(stmt, null, decl, Collections.emptySet(),
		// overappr);
		assert resultBuilder.getLrVal() == null;
		assert resultBuilder.getAuxVars().isEmpty();
		return resultBuilder.build();
	}

	/**
	 * Handle postfix increment and decrement operators according to Section 6.5.2.4 of C11. We translate the expression
	 * <code>LV++</code> to an auxiliary variable <code>t~post</code> and add to the resulting {@link ExpressionResult}
	 * the two assignments <code>t~post := LV</code> and <code>LV := t~post + 1</code>. Hence the auxiliary variable
	 * <code>t~post</code> stores the old value of the object to which the lvalue <code>LV</code> refers.
	 */
	private Result handlePostfixIncrementAndDecrement(final Dispatcher main, final ILocation loc, final int postfixOp,
			ExpressionResult exprRes, final IASTNode hook) {
		assert !exprRes.mLrVal.isBoogieBool();
		final LRValue modifiedLValue = exprRes.mLrVal;
		exprRes = exprRes.switchToRValueIfNecessary(main, loc, hook);
		// final ExpressionResult result =
		// ExpressionResult.copyStmtDeclAuxvarOverapprox(exprRes);
		final ExpressionResultBuilder builder1 =
				new ExpressionResultBuilder().addAllExceptLrValue(exprRes).setLrVal(exprRes.getLrValue());

		// In this case we need a temporary variable for the old value
		// final String tmpName = mNameHandler.getTempVarUID(SFO.AUXVAR.POST_MOD,
		// exprRes.mLrVal.getCType());
		// final ASTType tmpIType = mTypeHandler.cType2AstType(loc,
		// exprRes.mLrVal.getCType());
		// final VariableDeclaration tmpVar = SFO.getTempVarVariableDeclaration(tmpName,
		// tmpIType, loc);
		final AuxVarInfo auxvar =
				AuxVarInfo.constructAuxVarInfo(loc, main, exprRes.mLrVal.getCType(), SFO.AUXVAR.POST_MOD);
		// result.mAuxVars.put(tmpVar, loc);
		// result.mDecl.add(tmpVar);
		builder1.addDeclaration(auxvar.getVarDec());
		// builder1.putAuxVar(auxvar.getVarDec(), loc);
		builder1.addAuxVar(auxvar);

		// assign the old value to the temporary variable
		final AssignmentStatement assignStmt;
		{
			final LeftHandSide[] tmpAsLhs = new LeftHandSide[] { auxvar.getLhs() };
			final Expression[] oldValue = new Expression[] { exprRes.mLrVal.getValue() };
			assignStmt = StatementFactory.constructAssignmentStatement(loc, tmpAsLhs, oldValue);
		}
		// result.mStmt.add(assignStmt);
		builder1.addStatement(assignStmt);
		final CType oType = exprRes.mLrVal.getCType().getUnderlyingType();
		final RValue tmpRValue = new RValue(auxvar.getExp(), oType);

		final int op;
		if (postfixOp == IASTUnaryExpression.op_postFixIncr) {
			op = IASTBinaryExpression.op_plus;
		} else if (postfixOp == IASTUnaryExpression.op_postFixDecr) {
			op = IASTBinaryExpression.op_minus;
		} else {
			throw new AssertionError("no postfix");
		}

		// in-/decremented value
		final ExpressionResult intermediateResult = builder1.build();
		// final Expression valueXcremented = constructXcrementedValue(main, loc,
		// result, oType, op, tmpRValue.getValue());
		final Expression valueXcremented =
				constructXcrementedValue(main, loc, intermediateResult, oType, op, tmpRValue.getValue(), hook);
		final ExpressionResultBuilder builder2 = new ExpressionResultBuilder().addAllExceptLrValue(intermediateResult);

		final RValue rhs = new RValue(valueXcremented, oType, false, false);
		builder2.setLrVal(rhs);
		// final ExpressionResult assign = makeAssignment(main, loc, result.mStmt,
		// modifiedLValue, rhs, result.mDecl,
		// result.mAuxVars, result.mOverappr);
		final ExpressionResult assign =
				makeAssignment(main, loc, modifiedLValue, Collections.emptyList(), builder2.build(), hook);
		final ExpressionResultBuilder builder3 = new ExpressionResultBuilder().addAllExceptLrValue(assign);
		// assign.mLrVal = tmpRValue;
		builder3.setLrVal(tmpRValue);
		// return assign;
		return builder3.build();
	}

	/**
	 * Handle prefix increment and decrement operators according to Section 6.5.3.1 of C11. We translate the expression
	 * <code>++LV</code> to an auxiliary variable <code>t~pre</code> and add to the resulting {@link ExpressionResult}
	 * the two assignments <code>t~pre := LV+1</code> and <code>LV := t~pre</code>. Hence, the auxiliary variable
	 * <code>t~pre</code> stores the new value of the object to which the lvalue <code>LV</code> refers.
	 *
	 * Question: Why are we doing this complicated replacement and do not replace <code>++LV</code> by
	 * <code>LV + 1</code> ? Answer: We want to be ready for dealing with cases where there are several pre/post
	 * increment/decrement operations in one expression. We might extend our implementation in a way where the operation
	 * is done at a certain sequence point or all evaluation orders are considered.
	 */
	private Result handlePrefixIncrementAndDecrement(final Dispatcher main, final int prefixOp, final ILocation loc,
			ExpressionResult exprRes, final IASTNode hook) {
		assert !exprRes.mLrVal.isBoogieBool();
		final LRValue modifiedLValue = exprRes.mLrVal;
		exprRes = exprRes.switchToRValueIfNecessary(main, loc, hook);
		// final ExpressionResult result =
		// ExpressionResult.copyStmtDeclAuxvarOverapprox(exprRes);
		final ExpressionResultBuilder builder1 = new ExpressionResultBuilder();
		builder1.addAllExceptLrValue(exprRes);

		// In this case we need a temporary variable for the new value
		// final String tmpName = mNameHandler.getTempVarUID(SFO.AUXVAR.PRE_MOD,
		// exprRes.mLrVal.getCType());
		// final ASTType tmpIType = mTypeHandler.cType2AstType(loc,
		// exprRes.mLrVal.getCType());
		// final VariableDeclaration tmpVar = SFO.getTempVarVariableDeclaration(tmpName,
		// tmpIType, loc);
		final AuxVarInfo auxvar =
				AuxVarInfo.constructAuxVarInfo(loc, main, exprRes.getLrValue().getCType(), SFO.AUXVAR.PRE_MOD);
		// result.mAuxVars.put(tmpVar, loc);
		// result.mDecl.add(tmpVar);
		builder1.addDeclaration(auxvar.getVarDec());
		// builder1.putAuxVar(auxvar.getVarDec(), loc);
		builder1.addAuxVar(auxvar);

		final int op;
		if (prefixOp == IASTUnaryExpression.op_prefixIncr) {
			op = IASTBinaryExpression.op_plus;
		} else if (prefixOp == IASTUnaryExpression.op_prefixDecr) {
			op = IASTBinaryExpression.op_minus;
		} else {
			throw new AssertionError("no prefix");
		}

		final CType oType = exprRes.mLrVal.getCType().getUnderlyingType();
		// in-/decremented value
		final ExpressionResult intermediateResult = builder1.build();
		final Expression valueXcremented =
				constructXcrementedValue(main, loc, intermediateResult, oType, op, exprRes.mLrVal.getValue(), hook);
		// constructXcrementedValue(main, loc, result, oType, op,
		// exprRes.mLrVal.getValue());
		final ExpressionResultBuilder builder2 = new ExpressionResultBuilder().addAllExceptLrValue(intermediateResult)
				.setLrVal(intermediateResult.getLrValue());

		// assign the old value to the temporary variable
		final AssignmentStatement assignStmt;
		{
			final LeftHandSide[] tmpAsLhs = new LeftHandSide[] { auxvar.getLhs() };
			final Expression[] newValue = new Expression[] { valueXcremented };
			assignStmt = StatementFactory.constructAssignmentStatement(loc, tmpAsLhs, newValue);
		}
		// result.mStmt.add(assignStmt);
		builder2.addStatement(assignStmt);

		final RValue rhs = new RValue(valueXcremented, oType, false, false);
		// final ExpressionResult assign = makeAssignment(main, loc, result.mStmt,
		// modifiedLValue, rhs, result.mDecl,
		// result.mAuxVars, result.mOverappr);
		builder2.setLrVal(rhs);
		final ExpressionResult assign =
				makeAssignment(main, loc, modifiedLValue, Collections.emptyList(), builder2.build(), hook);
		final ExpressionResultBuilder builder3 = new ExpressionResultBuilder();
		builder3.addAllExceptLrValue(assign);

		final RValue tmpRValue = new RValue(auxvar.getExp(), oType);
		// assign.mLrVal = tmpRValue;
		// return assign;
		builder3.setLrVal(tmpRValue);
		return builder3.build();
	}

	private void markAsIntFromPointer(final ILocation loc, final String lId, final IASTNode hook) {
		final String cId4Boogie = mSymbolTable.getCIdForBoogieId(lId);
		final SymbolTableValue old = mSymbolTable.findCSymbol(hook, cId4Boogie);
		final SymbolTableValue newSTV = old.createMarkedIsIntFromPointer();
		mSymbolTable.storeCSymbol(hook, cId4Boogie, newSTV);
	}

	private void processTUchild(final Dispatcher main, final ArrayList<Declaration> decl, final IASTNode child) {
		{
			final ExpressionResultBuilder acslResultBuilder = new ExpressionResultBuilder();
			// checkForACSL(main, null, decl, child, null);
			checkForACSL(main, acslResultBuilder, child, null, false);
			decl.addAll(acslResultBuilder.getDeclarations());
		}
		final Result childRes = main.dispatch(child);

		if (childRes instanceof DeclarationResult) {
			// we have to add a global variable
			final DeclarationResult rd = (DeclarationResult) childRes;
			for (final CDeclaration cd : rd.getDeclarations()) {
				// mDeclarationsGlobalInBoogie.put(mSymbolTable.getBoogieDeclOfCDecl(cd), cd);

				final Declaration boogieDecl = mSymbolTable.getBoogieDeclForCDecl(cd);
				if (boogieDecl instanceof VariableDeclaration) {
					mStaticObjectsHandler.addGlobalVariableDeclaration((VariableDeclaration) boogieDecl, cd);
				} else {
					throw new AssertionError("TODO: handle this case!");
				}
			}
		} else {
			if (childRes instanceof SkipResult) {
				return;
			}
			if (childRes.node == null) {
				return;
			}
			assert childRes.getClass() == Result.class;
			assert childRes.node != null;
			decl.add((Declaration) childRes.node);
		}
	}

	/**
	 * Handles the declaration of an enum type (-d variable).
	 *
	 * @param main
	 *            a reference to the main dispatcher.
	 * @param node
	 *            the node holding the enum declaration.
	 * @return the translation of this declaration.
	 */
	protected void handleEnumDeclaration(final Dispatcher main, final IASTSimpleDeclaration node) {
		final Result r = main.dispatch(node.getDeclSpecifier());
		assert r instanceof TypesResult;
		final TypesResult rt = (TypesResult) r;
		assert rt.cType instanceof CEnum;
		final CEnum cEnum = (CEnum) rt.cType;
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		final CPrimitive typeOfEnumIdentifiers = new CPrimitive(CPrimitive.CPrimitives.INT);
		final ASTType enumAstType = mTypeHandler.cType2AstType(loc, typeOfEnumIdentifiers);
		final String enumId = cEnum.getIdentifier();
		final Expression[] enumDomain = new Expression[cEnum.getFieldCount()];

		Expression oldValue = null;
		Integer oldValueInt = -1;

		// C standard says: "The identifiers in an enumerator list are declared
		// as constants that have type int ..."

		for (int i = 0; i < cEnum.getFieldCount(); i++) {
			final String fId = cEnum.getFieldIds()[i];
			final String bId = enumId + "~" + fId;
			final VarList vl = new VarList(loc, new String[] { bId }, enumAstType);
			final ConstDeclaration cd = new ConstDeclaration(loc, new Attribute[0], false, vl, null, false);

			mStaticObjectsHandler.addGlobalConstDeclaration(cd, new CDeclaration(cEnum, fId));

			final Expression l = ExpressionFactory.constructIdentifierExpression(loc,
					mBoogieTypeHelper.getBoogieTypeForBoogieASTType(enumAstType), bId,
					new DeclarationInformation(StorageClass.GLOBAL, null));
			Expression newValue = oldValue;
			Integer newValueInt = oldValueInt;
			if (oldValue == null && cEnum.getFieldValue(fId) == null) {
				final Expression zero = mExpressionTranslation.constructLiteralForIntegerType(loc,
						typeOfEnumIdentifiers, BigInteger.ZERO);
				newValue = zero;
				newValueInt = 0;
			} else if (cEnum.getFieldValue(fId) == null) {
				newValueInt = oldValueInt + 1;
				newValue = mExpressionTranslation.constructLiteralForIntegerType(loc, typeOfEnumIdentifiers,
						new BigInteger(newValueInt.toString()));

			} else {
				final BigInteger bi = mExpressionTranslation.extractIntegerValue(cEnum.getFieldValue(fId),
						typeOfEnumIdentifiers, node);
				if (bi == null) {
					throw new AssertionError("not an integer constant: " + cEnum.getFieldValue(fId));
				}
				newValueInt = bi.intValue();
				newValue = cEnum.getFieldValue(fId);
			}
			oldValue = newValue;
			oldValueInt = newValueInt;
			enumDomain[i] = newValue;
			mAxioms.add(new Axiom(loc, new Attribute[0],
					ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, l, newValue)));
			mSymbolTable.storeCSymbol(node, fId,
					new SymbolTableValue(bId, cd,
							new CDeclaration(typeOfEnumIdentifiers, fId,
									scConstant2StorageClass(node.getDeclSpecifier().getStorageClass())),
							DeclarationInformation.DECLARATIONINFO_GLOBAL, node, false, newValue));
		}
	}

	protected CStorageClass scConstant2StorageClass(final int storageClass) {
		switch (storageClass) {
		case IASTDeclSpecifier.sc_auto:
			return CStorageClass.AUTO;
		case IASTDeclSpecifier.sc_extern:
			return CStorageClass.EXTERN;
		case IASTDeclSpecifier.sc_mutable:
			return CStorageClass.MUTABLE;
		case IASTDeclSpecifier.sc_register:
			return CStorageClass.REGISTER;
		case IASTDeclSpecifier.sc_static:
			return CStorageClass.STATIC;
		case IASTDeclSpecifier.sc_typedef:
			return CStorageClass.TYPEDEF;
		case IASTDeclSpecifier.sc_unspecified:
			return CStorageClass.UNSPECIFIED;
		default:
			throw new AssertionError("should not happen");
		}
	}

	/**
	 * Handle additive operators according to Sections 6.5.6 of C11. Assumes that left (resp. right) are the results
	 * from handling the operands. Requires that the {@link LRValue} of operands is an {@link RValue} (i.e.,
	 * switchToRValueIfNecessary was applied if needed). requires that the Boogie expressions in left (resp. right) are
	 * a non-boolean representation of these results (i.e., rexBoolToIntIfNecessary() has already been applied if
	 * needed).
	 *
	 * @param lhs
	 *            is non-null iff we haven an assignment
	 */
	ExpressionResult handleAdditiveOperation(final Dispatcher main, final ILocation loc, final LRValue lhs,
			final int op, final ExpressionResult left, final ExpressionResult right, final IASTNode hook) {
		assert left.mLrVal instanceof RValue : "no RValue";
		assert right.mLrVal instanceof RValue : "no RValue";

		CType lType = left.mLrVal.getCType().getUnderlyingType();
		final CType rType = right.mLrVal.getCType().getUnderlyingType();

		if (lType instanceof CArray && rType.isArithmeticType()) {
			// arrays decay to pointers in this case
			// assert ((CArray) lType).getDimensions().length == 1 : "TODO: think about this
			// case";
			assert !(((CArray) lType).getBound().getCType() instanceof CArray) : "TODO: think about this case";
			final CType valueType = ((CArray) lType).getValueType().getUnderlyingType();
			convert(loc, left, new CPointer(valueType));
			lType = left.mLrVal.getCType().getUnderlyingType();
		}

		ExpressionResult intermediateResult;
		final Expression expr;
		final CType typeOfResult;
		if (lType.isArithmeticType() && rType.isArithmeticType()) {
			mExpressionTranslation.usualArithmeticConversions(loc, left, right);
			typeOfResult = left.mLrVal.getCType();
			assert typeOfResult.equals(right.mLrVal.getCType());
			intermediateResult = ExpressionResult.copyStmtDeclAuxvarOverapprox(left, right);
			addIntegerBoundsCheck(main, loc, intermediateResult, (CPrimitive) typeOfResult, op, hook,
					left.mLrVal.getValue(), right.mLrVal.getValue());
			expr = mExpressionTranslation.constructArithmeticExpression(loc, op, left.mLrVal.getValue(),
					(CPrimitive) typeOfResult, right.mLrVal.getValue(), (CPrimitive) typeOfResult);
		} else if (lType instanceof CPointer && rType.isArithmeticType()) {
			typeOfResult = left.mLrVal.getCType();
			final CType pointsToType = ((CPointer) typeOfResult).pointsToType;
			intermediateResult = ExpressionResult.copyStmtDeclAuxvarOverapprox(left, right);
			final ExpressionResult re = doPointerArithmeticWithConversion(main, op, loc, left.mLrVal.getValue(),
					(RValue) right.mLrVal, pointsToType, hook);
			intermediateResult.addAll(re);
			expr = re.mLrVal.getValue();
			addOffsetInBoundsCheck(main, loc, expr, intermediateResult);
		} else if (lType.isArithmeticType() && rType instanceof CPointer) {
			if (op != IASTBinaryExpression.op_plus && op != IASTBinaryExpression.op_plusAssign) {
				throw new AssertionError("lType arithmetic, rType CPointer only legal if op is plus");
			}
			typeOfResult = right.mLrVal.getCType();
			final CType pointsToType = ((CPointer) typeOfResult).pointsToType;
			intermediateResult = ExpressionResult.copyStmtDeclAuxvarOverapprox(left, right);
			final ExpressionResult re = doPointerArithmeticWithConversion(main, op, loc, right.mLrVal.getValue(),
					(RValue) left.mLrVal, pointsToType, hook);
			intermediateResult.addAll(re);
			expr = re.mLrVal.getValue();
			addOffsetInBoundsCheck(main, loc, expr, intermediateResult);
		} else if (lType instanceof CPointer && rType instanceof CPointer) {
			if (op != IASTBinaryExpression.op_minus && op != IASTBinaryExpression.op_minusAssign) {
				throw new AssertionError("lType arithmetic, rType CPointer only legal if op is minus");
			}
			// C11 6.5.6.9 says
			// "The size of the result is implementation-defined,
			// and its type (a signed integer type) is ptrdiff_t defined in
			// the <stddef.h> header."
			// We randomly choose the type whose Boogie translation we use to
			// represent pointer components.
			typeOfResult = mExpressionTranslation.getCTypeOfPointerComponents();
			intermediateResult = ExpressionResult.copyStmtDeclAuxvarOverapprox(left, right);
			CType pointsToType;
			{
				final CType leftPointsToType = ((CPointer) lType).pointsToType;
				final CType rightPointsToType = ((CPointer) rType).pointsToType;
				if (!leftPointsToType.equals(rightPointsToType)) {
					// TODO: Matthias 2015-09-08: Maybe this is too strict and we
					// have to check leftPointsToType.isCompatibleWith(rightPointsToType)
					throw new UnsupportedOperationException(
							"incompatible pointers: pointsto " + leftPointsToType + " " + rightPointsToType);
				}
				pointsToType = leftPointsToType;
			}
			addBaseEqualityCheck(main, loc, left.mLrVal.getValue(), right.mLrVal.getValue(), intermediateResult);
			expr = doPointerSubtraction(main, loc, left.mLrVal.getValue(), right.mLrVal.getValue(), pointsToType, hook);

		} else {
			throw new UnsupportedOperationException("non-standard case of pointer arithmetic");
		}
		final RValue rval = new RValue(expr, typeOfResult, false, false);

		ExpressionResult intermediateResult2;
		/*
		 * if we had a StringLiteralResult as input, we have to restore the StringLiteralResult from the
		 * ExpressionResult.
		 */
		if (left instanceof StringLiteralResult) {
			assert lhs == null : "unforseen case";

			// result = new StringLiteralResult(result.getStatements(), null,
			// result.getDeclarations(),
			// result.getAuxVars(), result.getOverapprs(), ((StringLiteralResult)
			// left).getAuxVarName(),
			// ((StringLiteralResult) left).getLiteralString(),
			// ((StringLiteralResult) left).overApproximatesLongStringLiteral());
			intermediateResult2 = new StringLiteralResult(
					// intermediateResult.getStatements(),
					intermediateResult.getLrValue(), // null,
					// intermediateResult.getDeclarations(),
					// intermediateResult.getAuxVars(),
					intermediateResult.getOverapprs(), ((StringLiteralResult) left).getAuxVar(),
					((StringLiteralResult) left).getLiteralString(),
					((StringLiteralResult) left).overApproximatesLongStringLiteral());

			intermediateResult.getDeclarations().forEach(decl -> mStaticObjectsHandler
					.addGlobalVarDeclarationWithoutCDeclaration((VariableDeclaration) decl));
			mStaticObjectsHandler.addStatementsForUltimateInit(intermediateResult.getStatements());

		} else {
			intermediateResult2 = intermediateResult;
		}

		switch (op) {
		case IASTBinaryExpression.op_plus:
		case IASTBinaryExpression.op_minus: {
			assert lhs == null : "no assignment";
			intermediateResult2.mLrVal = rval;
			return intermediateResult2;
		}
		case IASTBinaryExpression.op_plusAssign:
		case IASTBinaryExpression.op_minusAssign: {
			// result = makeAssignment(main, loc, result.mStmt, lhs, rval, result.mDecl,
			// result.mAuxVars,
			// result.mOverappr);
			intermediateResult2.mLrVal = rval;
			final ExpressionResult result =
					makeAssignment(main, loc, lhs, Collections.emptyList(), intermediateResult2, hook);
			return result;
		}
		default:
			throw new AssertionError("no additive operation " + op);
		}
	}

	/**
	 * Handle equality operators according to Section 6.5.7 of C11. Assumes that left (resp. right) are the results from
	 * handling the operands. Requires that the {@link LRValue} of operands is an {@link RValue} (i.e.,
	 * switchToRValueIfNecessary was applied if needed). requires that the Boogie expressions in left (resp. right) are
	 * a non-boolean representation of these results (i.e., rexBoolToIntIfNecessary() has already been applied if
	 * needed).
	 *
	 * @param lhs
	 *            is non-null iff we haven an assignment
	 */
	ExpressionResult handleBitshiftOperation(final Dispatcher main, final ILocation loc, final LRValue lhs,
			final int op, final ExpressionResult left, final ExpressionResult right, final IASTNode hook) {
		assert left.mLrVal instanceof RValue : "no RValue";
		assert right.mLrVal instanceof RValue : "no RValue";
		final CType lType = left.mLrVal.getCType().getUnderlyingType();
		final CType rType = right.mLrVal.getCType().getUnderlyingType();
		if (!rType.isIntegerType() || !lType.isIntegerType()) {
			throw new UnsupportedOperationException("operands have to have integer types");
		}
		mExpressionTranslation.doIntegerPromotion(loc, left);
		final CPrimitive typeOfResult = (CPrimitive) left.mLrVal.getCType();
		convert(loc, right, typeOfResult);
		final Expression expr = mExpressionTranslation.constructBinaryBitwiseExpression(loc, op, left.mLrVal.getValue(),
				typeOfResult, right.mLrVal.getValue(), typeOfResult, hook);
		final RValue rval = new RValue(expr, typeOfResult, false, false);
		switch (op) {
		case IASTBinaryExpression.op_shiftLeft:
		case IASTBinaryExpression.op_shiftRight: {
			assert lhs == null : "no assignment";
			final ExpressionResult result = ExpressionResult.copyStmtDeclAuxvarOverapprox(left, right);
			if (op == IASTBinaryExpression.op_shiftLeft) {
				addIntegerBoundsCheck(main, loc, result, (CPrimitive) rval.getCType(), op, hook, left.mLrVal.getValue(),
						right.mLrVal.getValue());
			}
			result.mLrVal = rval;
			return result;
		}
		case IASTBinaryExpression.op_shiftLeftAssign:
		case IASTBinaryExpression.op_shiftRightAssign: {
			final ExpressionResult copy = ExpressionResult.copyStmtDeclAuxvarOverapprox(left, right);
			if (op == IASTBinaryExpression.op_shiftLeftAssign) {
				addIntegerBoundsCheck(main, loc, copy, (CPrimitive) rval.getCType(), op, hook, left.mLrVal.getValue(),
						right.mLrVal.getValue());
			}

			copy.mLrVal = rval;

			final ExpressionResult result =
					// makeAssignment(main, loc, copy.mStmt, lhs, rval, copy.mDecl, copy.mAuxVars,
					// copy.mOverappr);
					makeAssignment(main, loc, lhs, Collections.emptyList(), copy, hook);
			return result;
		}
		default:
			throw new AssertionError("no bitshift " + op);
		}
	}

	/**
	 * Handle bitwise AND, bitwise XOR, and bitwise OR operators according to sections 6.5.10, 6.5.11, 6.5.12 of C11.
	 * Assumes that left (resp. right) are the results from handling the operands. Requires that the {@link LRValue} of
	 * operands is an {@link RValue} (i.e., switchToRValueIfNecessary was applied if needed). requires that the Boogie
	 * expressions in left (resp. right) are a non-boolean representation of these results (i.e.,
	 * rexBoolToIntIfNecessary() has already been applied if needed).
	 *
	 * @param lhs
	 *            is non-null iff we haven an assignment
	 */
	ExpressionResult handleBitwiseArithmeticOperation(final Dispatcher main, final ILocation loc, final LRValue lhs,
			final int op, final ExpressionResult left, final ExpressionResult right, final IASTNode hook) {
		assert left.mLrVal instanceof RValue : "no RValue";
		assert right.mLrVal instanceof RValue : "no RValue";
		final CType lType = left.mLrVal.getCType().getUnderlyingType();
		final CType rType = right.mLrVal.getCType().getUnderlyingType();
		if (!rType.isIntegerType() || !lType.isIntegerType()) {
			throw new UnsupportedOperationException("operands have to have integer types");
		}
		mExpressionTranslation.usualArithmeticConversions(loc, left, right);
		final CPrimitive typeOfResult = (CPrimitive) left.mLrVal.getCType();
		assert typeOfResult.equals(left.mLrVal.getCType());
		final Expression expr = mExpressionTranslation.constructBinaryBitwiseExpression(loc, op, left.mLrVal.getValue(),
				typeOfResult, right.mLrVal.getValue(), typeOfResult, hook);
		final RValue rval = new RValue(expr, typeOfResult, false, false);
		switch (op) {
		case IASTBinaryExpression.op_binaryAnd:
		case IASTBinaryExpression.op_binaryXor:
		case IASTBinaryExpression.op_binaryOr: {
			assert lhs == null : "no assignment";
			final ExpressionResult result = ExpressionResult.copyStmtDeclAuxvarOverapprox(left, right);
			result.mLrVal = rval;
			return result;
		}
		case IASTBinaryExpression.op_binaryAndAssign:
		case IASTBinaryExpression.op_binaryXorAssign:
		case IASTBinaryExpression.op_binaryOrAssign: {
			final ExpressionResult copy = ExpressionResult.copyStmtDeclAuxvarOverapprox(left, right);

			copy.mLrVal = rval;

			final ExpressionResult result =
					// makeAssignment(main, loc, copy.mStmt, lhs, rval, copy.mDecl, copy.mAuxVars,
					// copy.mOverappr);
					makeAssignment(main, loc, lhs, Collections.emptyList(), copy, hook);
			return result;
		}
		default:
			throw new AssertionError("no bitwise arithmetic operation " + op);
		}
	}

	/**
	 * Handle conditional operator according to Section 6.5.15 of C11. Assumes that opCondition, opPositive, and
	 * opNegative are the results from handling the operands. Requires that the {@link LRValue} of operands is an
	 * {@link RValue} (i.e., switchToRValueIfNecessary was applied if needed). TODO: Check all corner cases, write some
	 * testfiles.
	 *
	 *
	 *
	 */
	ExpressionResult handleConditionalOperator(final ILocation loc, final Dispatcher main,
			final ExpressionResult opConditionRaw, final ExpressionResult opPositiveRaw,
			final ExpressionResult opNegativeRaw, final IASTNode hook) {

		final ExpressionResult opCondition = opConditionRaw;
		opCondition.rexIntToBoolIfNecessary(loc, mExpressionTranslation, mMemoryHandler);

		ExpressionResult opPositive = opPositiveRaw;
		ExpressionResult opNegative = opNegativeRaw;

		opPositive.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
		opNegative.rexBoolToIntIfNecessary(loc, mExpressionTranslation);

		/*
		 * C11 6.5.15.2 The first operand shall have scalar type.
		 */
		if (!opCondition.getLrValue().getCType().isScalarType()) {
			throw new IncorrectSyntaxException(loc, "first operand of a conditional operator must have scalar type");
		}

		/*
		 * C11 6.5.15.3 One of the following shall hold for the second and third operands: <li> both operands have
		 * arithmetic type; <li> both operands have the same structure or union type; <li> both operands have void type;
		 * <li> both operands are pointers to qualified or unqualified versions of compatible types; <li> one operand is
		 * a pointer and the other is a null pointer constant; or <li> one operand is a pointer to an object type and
		 * the other is a pointer to a qualified or unqualified version of void.
		 */

		/*
		 * C11 6.5.15.4 The first operand is evaluated; there is a sequence point between its evaluation and the
		 * evaluation of the second or third operand (whichever is evaluated). The second operand is evaluated only if
		 * the first compares unequal to 0; the third operand is evaluated only if the first compares equal to 0; the
		 * result is the value of the second or third operand (whichever is evaluated), converted to the type described
		 * below. 110)
		 *
		 * --> we translate this by a Boogie if-statement, such that the side effects of the evaluation of each C
		 * expression go into the respective branch of the Boogie if statement.
		 */

		/*
		 * C11 6.5.15.5 If both the second and third operands have arithmetic type, the result type that would be
		 * determined by the usual arithmetic conversions, were they applied to those two operands, is the type of the
		 * result. If both the operands have structure or union type, the result has that type. If both operands have
		 * void type, the result has void type.
		 */

		/*
		 * C11 6.5.15.6 If both the second and third operands are pointers or one is a null pointer constant and the
		 * other is a pointer, the result type is a pointer to a type qualified with all the type qualifiers of the
		 * types referenced by both operands. Furthermore, if both operands are pointers to compatible types or to
		 * differently qualified versions of compatible types, the result type is a pointer to an appropriately
		 * qualified version of the composite type; if one operand is a null pointer constant, the result has the type
		 * of the other operand; otherwise, one operand is a pointer to void or a qualified version of void, in which
		 * case the result type is a pointer to an appropriately qualified version of void.
		 *
		 * TODO: this is only partially implemented, for example we are not doing anything about the qualifiers,
		 * currently.
		 */

		/*
		 * Treatment of the cases where one or both branches have void type and the LRValue of the dispatch result of
		 * the branch is is null: We give a dummy LRValue, whose BoogieType is a type error so it cannot be used
		 * further.
		 */

		boolean secondArgIsVoid = false;
		boolean thirdArgIsVoid = false;

		if (!opPositive.hasLRValue()) {
			opPositive.mLrVal = new RValue(ExpressionFactory.createVoidDummyExpression(loc),
					// dummyVoidAuxVar.getExp(),
					new CPrimitive(CPrimitives.VOID));
			secondArgIsVoid = true;
		}
		if (!opNegative.hasLRValue()) {
			opNegative.mLrVal = new RValue(ExpressionFactory.createVoidDummyExpression(loc),
					// dummyVoidAuxVar.getExp(),
					new CPrimitive(CPrimitives.VOID));
			thirdArgIsVoid = true;
		}

		final CType resultCType;
		if (opPositive.getLrValue().getCType().isArithmeticType()
				&& opNegative.getLrValue().getCType().isArithmeticType()) {
			/*
			 * C11 6.5.15.5: If both the second and third operands have arithmetic type, the result type that would be
			 * determined by the usual arithmetic conversions, were they applied to those two operands, is the type of
			 * the result.
			 */
			mExpressionTranslation.usualArithmeticConversions(loc, opPositive, opNegative);
			resultCType = opPositive.getLrValue().getCType();
		} else if (secondArgIsVoid && thirdArgIsVoid) {
			/* C11 6.5.15.5 If both operands have void type, the result has void type. */
			resultCType = new CPrimitive(CPrimitives.VOID);
		} else if (opPositive.getLrValue().isNullPointerConstant()) {
			/* C11 6.5.15.6 if one operand is a null pointer constant, the result has the type of the other operand; */

			if (opNegative.getLrValue().getCType().getUnderlyingType() instanceof CPointer) {
				// convert the "0" to a pointer
				mExpressionTranslation.convertIntToPointer(loc, opPositive,
						(CPointer) opNegative.mLrVal.getCType().getUnderlyingType());
				resultCType = opNegative.getLrValue().getCType();
			} else if (opNegative.getLrValue().getCType().getUnderlyingType() instanceof CArray) {
				/* if one of the branches has pointer type and one has array type, the array decays to a pointer. */
				opNegative = opNegative.decayArrayToPointerIfNecessary(main, loc, hook);
				mExpressionTranslation.convertIntToPointer(loc, opPositive,
						(CPointer) opNegative.getLrValue().getCType().getUnderlyingType());
				resultCType = opNegative.getLrValue().getCType();
			} else {
				resultCType = opNegative.getLrValue().getCType();
			}

		} else if (opNegative.getLrValue().isNullPointerConstant()) {
			/* C11 6.5.15.6 if one operand is a null pointer constant, the result has the type of the other operand; */

			if (opPositive.getLrValue().getCType().getUnderlyingType() instanceof CPointer) {
				// convert the "0" to a pointer
				mExpressionTranslation.convertIntToPointer(loc, opNegative,
						(CPointer) opPositive.mLrVal.getCType().getUnderlyingType());
				resultCType = opPositive.getLrValue().getCType();
			} else if (opPositive.getLrValue().getCType().getUnderlyingType() instanceof CArray) {
				/* if one of the branches has pointer type and one has array type, the array decays to a pointer. */
				opPositive = opPositive.decayArrayToPointerIfNecessary(main, loc, hook);
				mExpressionTranslation.convertIntToPointer(loc, opNegative,
						(CPointer) opPositive.getLrValue().getCType().getUnderlyingType());
				resultCType = opPositive.getLrValue().getCType();
			} else {
				resultCType = opPositive.getLrValue().getCType();
			}
		} else {
			// default case: the types of the operands (should) match --> we choose one of them as the result CType
			resultCType = opPositive.getLrValue().getCType();
		}

		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();

		// TODO: a solution that checks if the void value is ever assigned would be nice, but unclear if necessary..
		// /*
		// * the value of this aux var may never be used outside the translation of this conditional operator.
		// * Using the aux var in the hope of detecting such errors easier. Otherwise one could just not make the
		// * assignment.
		// */
		// final AuxVarInfo dummyVoidAuxVar = AuxVarInfo.constructAuxVarInfo(loc, main, resultCType,
		// mTypeHandler.cType2AstType(loc, resultCType),
		// SFO.AUXVAR.DUMMY_VOID);
		// resultBuilder.addDeclaration(dummyVoidAuxVar.getVarDec());
		// resultBuilder.addAuxVar(dummyVoidAuxVar);

		resultBuilder.addAllExceptLrValue(opCondition);

		// auxvar that will hold the result of the ite expression
		final AuxVarInfo auxvar;
		if (resultCType.isVoidType()) {
			/* in this case we will not make any assignment, so we do not need the aux var */
			auxvar = null;
		} else {
			auxvar = AuxVarInfo.constructAuxVarInfo(loc, main, resultCType, SFO.AUXVAR.ITE);
			resultBuilder.addDeclaration(auxvar.getVarDec());
			resultBuilder.addAuxVar(auxvar);
		}

		// collect side effects of "then" branch
		final List<Statement> ifStatements = new ArrayList<>();
		{
			ifStatements.addAll(opPositive.mStmt);
			// if (!resultCType.isVoidType()) {
			if (!resultCType.isVoidType() && !secondArgIsVoid) {
				final LeftHandSide[] lhs = { auxvar.getLhs() };
				final Expression assignedVal = opPositive.getLrValue().getValue();
				final AssignmentStatement assignStmt =
						StatementFactory.constructAssignmentStatement(loc, lhs, new Expression[] { assignedVal });
				for (final Overapprox overapprItem : resultBuilder.getOverappr()) {
					overapprItem.annotate(assignStmt);
				}
				ifStatements.add(assignStmt);
			}
			resultBuilder.addAllExceptLrValueAndStatements(opPositive);
		}

		// collect side effects of "else" branch
		final List<Statement> elseStatements = new ArrayList<>();
		{
			elseStatements.addAll(opNegative.mStmt);
			if (!resultCType.isVoidType() && !thirdArgIsVoid) {
				final LeftHandSide[] lhs = { auxvar.getLhs() };
				final Expression assignedVal = opNegative.getLrValue().getValue();
				final AssignmentStatement assignStmt =
						StatementFactory.constructAssignmentStatement(loc, lhs, new Expression[] { assignedVal });
				for (final Overapprox overapprItem : resultBuilder.getOverappr()) {
					overapprItem.annotate(assignStmt);
				}
				elseStatements.add(assignStmt);
			}
			resultBuilder.addAllExceptLrValueAndStatements(opNegative);
		}
		final Statement ifStatement = new IfStatement(loc, opCondition.mLrVal.getValue(),
				ifStatements.toArray(new Statement[ifStatements.size()]),
				elseStatements.toArray(new Statement[elseStatements.size()]));
		for (final Overapprox overapprItem : resultBuilder.getOverappr()) {
			overapprItem.annotate(ifStatement);
		}
		resultBuilder.addStatement(ifStatement);

		if (!resultCType.isVoidType()) {
			/* the result has a value only if the result type is not void.. */
			resultBuilder.setLrVal(new RValue(auxvar.getExp(), resultCType));
		} else {
			// /* for better error detection we give the dummy void value here */ (edit: see the todo above)
			// resultBuilder.setLrVal(new RValue(dummyVoidAuxVar.getExp(), resultCType));
		}
		return resultBuilder.build();
	}

	/**
	 * Handle equality operators according to Section 6.5.9 of C11. Assumes that left (resp. right) are the results from
	 * handling the operands. Requires that the {@link LRValue} of operands is an {@link RValue} (i.e.,
	 * switchToRValueIfNecessary was applied if needed). requires that the Boogie expressions in left (resp. right) are
	 * a non-boolean representation of these results (i.e., rexBoolToIntIfNecessary() has already been applied if
	 * needed).
	 */
	ExpressionResult handleEqualityOperators(final Dispatcher main, final ILocation loc, final int op,
			final ExpressionResult left, final ExpressionResult right) {
		assert left.mLrVal instanceof RValue : "no RValue";
		assert right.mLrVal instanceof RValue : "no RValue";
		{
			final CType lType = left.mLrVal.getCType().getUnderlyingType();
			final CType rType = right.mLrVal.getCType().getUnderlyingType();
			// FIXME Matthias 2015-09-05: operation only legal if both have type
			// CPointer I guess the following implicit casts are a workaround
			// for arrays (or structs or union?)
			if (lType instanceof CPointer || rType instanceof CPointer) {
				if (!(lType instanceof CPointer)) {
					// FIXME: the following is a workaround for the null pointer
					convert(loc, left, new CPointer(new CPrimitive(CPrimitives.VOID)));
				}
				if (!(rType instanceof CPointer)) {
					// FIXME: the following is a workaround for the null pointer
					convert(loc, right, new CPointer(new CPrimitive(CPrimitives.VOID)));
				}
			} else if (lType.isArithmeticType() && rType.isArithmeticType()) {
				mExpressionTranslation.usualArithmeticConversions(loc, left, right);
			} else {
				throw new UnsupportedOperationException("unsupported " + rType + ", " + lType);
			}
		}
		// The result has type int (C11 6.5.9.1)
		final CPrimitive typeOfResult = new CPrimitive(CPrimitives.INT);
		final Expression expr = mExpressionTranslation.constructBinaryEqualityExpression(loc, op,
				left.mLrVal.getValue(), left.mLrVal.getCType(), right.mLrVal.getValue(), right.mLrVal.getCType());
		final RValue rval = new RValue(expr, typeOfResult, true, false);
		final ExpressionResult result = ExpressionResult.copyStmtDeclAuxvarOverapprox(left, right);
		result.mLrVal = rval;
		return result;
	}

	/**
	 * Handle multiplicative operators according to Sections 6.5.5 of C11. Assumes that left (resp. right) are the
	 * results from handling the operands. Requires that the {@link LRValue} of operands is an {@link RValue} (i.e.,
	 * switchToRValueIfNecessary was applied if needed). requires that the Boogie expressions in left (resp. right) are
	 * a non-boolean representation of these results (i.e., rexBoolToIntIfNecessary() has already been applied if
	 * needed).
	 *
	 * @param lhs
	 *            is non-null iff we haven an assignment
	 */
	ExpressionResult handleMultiplicativeOperation(final Dispatcher main, final ILocation loc, final LRValue lhs,
			final int op, final ExpressionResult left, final ExpressionResult right, final IASTNode hook) {
		assert left.mLrVal instanceof RValue : "no RValue";
		assert right.mLrVal instanceof RValue : "no RValue";
		final CType lType = left.mLrVal.getCType().getUnderlyingType();
		final CType rType = right.mLrVal.getCType().getUnderlyingType();
		if (!rType.isArithmeticType() || !lType.isArithmeticType()) {
			throw new UnsupportedOperationException("operands have to have integer types");
		}
		if (op == IASTBinaryExpression.op_divide || op == IASTBinaryExpression.op_modulo) {
			addDivisionByZeroCheck(main, loc, right);
		}
		mExpressionTranslation.usualArithmeticConversions(loc, left, right);
		final CPrimitive typeOfResult = (CPrimitive) left.mLrVal.getCType();
		assert typeOfResult.equals(right.mLrVal.getCType());

		ExpressionResult result = ExpressionResult.copyStmtDeclAuxvarOverapprox(left, right);
		switch (op) {
		case IASTBinaryExpression.op_multiply:
		case IASTBinaryExpression.op_divide:
		case IASTBinaryExpression.op_multiplyAssign:
		case IASTBinaryExpression.op_divideAssign: {
			addIntegerBoundsCheck(main, loc, result, typeOfResult, op, hook, left.mLrVal.getValue(),
					right.mLrVal.getValue());
			break;
		}
		case IASTBinaryExpression.op_modulo:
		case IASTBinaryExpression.op_moduloAssign: {
			// no integer bounds check needed
			break;
		}
		default:
			throw new AssertionError("no multiplicative " + op);
		}

		final Expression expr = mExpressionTranslation.constructArithmeticExpression(loc, op, left.mLrVal.getValue(),
				typeOfResult, right.mLrVal.getValue(), typeOfResult);
		final RValue rval = new RValue(expr, typeOfResult, false, false);

		switch (op) {
		case IASTBinaryExpression.op_multiply:
		case IASTBinaryExpression.op_divide:
		case IASTBinaryExpression.op_modulo: {
			assert lhs == null : "no assignment";
			result.mLrVal = rval;
			return result;
		}
		case IASTBinaryExpression.op_multiplyAssign:
		case IASTBinaryExpression.op_divideAssign:
		case IASTBinaryExpression.op_moduloAssign: {
			// result = makeAssignment(main, loc, result.mStmt, lhs, rval, result.mDecl,
			// result.mAuxVars,
			// result.mOverappr);
			result.mLrVal = rval;
			result = makeAssignment(main, loc, lhs, Collections.emptyList(), result, hook);
			return result;
		}
		default:
			throw new AssertionError("no multiplicative " + op);
		}
	}

	/**
	 * Handle relational operators according to Section 6.5.8 of C11. Assumes that left (resp. right) are the results
	 * from handling the operands. Requires that the {@link LRValue} of operands is an {@link RValue} (i.e.,
	 * switchToRValueIfNecessary was applied if needed).
	 */
	ExpressionResult handleRelationalOperators(final Dispatcher main, final ILocation loc, final int op,
			final ExpressionResult left, final ExpressionResult right) {
		assert left.mLrVal instanceof RValue : "no RValue";
		assert right.mLrVal instanceof RValue : "no RValue";
		left.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
		right.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
		final CType lType = left.mLrVal.getCType().getUnderlyingType();
		final CType rType = right.mLrVal.getCType().getUnderlyingType();

		final ExpressionResult result = ExpressionResult.copyStmtDeclAuxvarOverapprox(left, right);
		final Expression expr;
		if (lType instanceof CPrimitive && rType instanceof CPrimitive) {
			assert lType.isRealType() && rType.isRealType() : "no real type";
			mExpressionTranslation.usualArithmeticConversions(loc, left, right);
			expr = mExpressionTranslation.constructBinaryComparisonExpression(loc, op, left.mLrVal.getValue(),
					(CPrimitive) left.mLrVal.getCType(), right.mLrVal.getValue(), (CPrimitive) right.mLrVal.getCType());
		} else if (lType instanceof CPointer && rType instanceof CPointer) {
			final Expression baseEquality = constructPointerComponentRelation(loc, IASTBinaryExpression.op_equals,
					left.mLrVal.getValue(), right.mLrVal.getValue(), SFO.POINTER_BASE);
			final Expression offsetRelation = constructPointerComponentRelation(loc, op, left.mLrVal.getValue(),
					right.mLrVal.getValue(), SFO.POINTER_OFFSET);
			switch (mMemoryHandler.getPointerSubtractionAndComparisonValidityCheckMode()) {
			case ASSERTandASSUME:
				final Statement assertStm = new AssertStatement(loc, baseEquality);
				final Check chk = new Check(Spec.ILLEGAL_POINTER_ARITHMETIC);
				chk.annotate(assertStm);
				result.mStmt.add(assertStm);
				expr = offsetRelation;
				break;
			case ASSUME:
				final Statement assumeStm = new AssumeStatement(loc, baseEquality);
				result.mStmt.add(assumeStm);
				expr = offsetRelation;
				break;
			case IGNORE:
				// use conjunction
				expr = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND, baseEquality, offsetRelation);
				// TODO: Do not use conjunction. Use nondeterministic value
				// if baseEquality does not hold.
				break;
			default:
				throw new AssertionError("unknown value");
			}

		} else {
			throw new UnsupportedOperationException("unsupported " + rType + ", " + lType);
		}
		// The result has type int (C11 6.5.8.6)
		final CPrimitive typeOfResult = new CPrimitive(CPrimitives.INT);
		final RValue rval = new RValue(expr, typeOfResult, true, false);
		result.mLrVal = rval;
		return result;
	}

	/**
	 * Handle unary arithmetic operators according to Section 6.5.3.3 of C11. Assumes that left (resp. right) are the
	 * results from handling the operands. Requires that the {@link LRValue} of operands is an {@link RValue} (i.e.,
	 * switchToRValueIfNecessary was applied if needed).
	 */
	ExpressionResult handleUnaryArithmeticOperators(final Dispatcher main, final ILocation loc, final int op,
			final ExpressionResult operand, final IASTNode hook) {
		assert operand.mLrVal instanceof RValue : "no RValue";
		final CType inputType = operand.mLrVal.getCType().getUnderlyingType();

		switch (op) {
		case IASTUnaryExpression.op_not: {
			if (!inputType.isScalarType()) {
				throw new IllegalArgumentException("scalar type required");
			}
			final Expression negated;
			if (operand.mLrVal.isBoogieBool()) {
				// in Boogie already represented by bool, we only negate
				negated = ExpressionFactory.constructUnaryExpression(loc, UnaryExpression.Operator.LOGICNEG,
						operand.mLrVal.getValue());
			} else {
				final Expression rhsOfComparison;
				if (inputType instanceof CPointer) {
					rhsOfComparison = mExpressionTranslation.constructNullPointer(loc);
				} else if (inputType instanceof CEnum) {
					final CPrimitive intType = new CPrimitive(CPrimitives.INT);
					rhsOfComparison = mExpressionTranslation.constructZero(loc, intType);
				} else if (inputType instanceof CPrimitive) {
					rhsOfComparison = mExpressionTranslation.constructZero(loc, inputType);
				} else {
					throw new AssertionError("illegal case");
				}
				negated = mExpressionTranslation.constructBinaryEqualityExpression(loc, IASTBinaryExpression.op_equals,
						operand.mLrVal.getValue(), inputType, rhsOfComparison, inputType);

			}
			final ExpressionResult result = ExpressionResult.copyStmtDeclAuxvarOverapprox(operand);
			// C11 6.5.3.3.5 The result has type int.
			final CPrimitive resultType = new CPrimitive(CPrimitives.INT);
			// type of Operator.COMPEQ expression is bool
			final boolean isBoogieBool = true;
			final RValue rval = new RValue(negated, resultType, isBoogieBool);
			result.mLrVal = rval;
			return result;
		}
		case IASTUnaryExpression.op_plus: {
			if (!inputType.isArithmeticType()) {
				throw new UnsupportedOperationException("arithmetic type required");
			}
			if (inputType.isArithmeticType()) {
				operand.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
				mExpressionTranslation.doIntegerPromotion(loc, operand);
			}
			return operand;
		}
		case IASTUnaryExpression.op_minus:
		case IASTUnaryExpression.op_tilde:
			if (!inputType.isArithmeticType()) {
				throw new UnsupportedOperationException("arithmetic type required");
			}
			operand.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			mExpressionTranslation.doIntegerPromotion(loc, operand);
			final CPrimitive resultType = (CPrimitive) operand.mLrVal.getCType();
			final ExpressionResult result = ExpressionResult.copyStmtDeclAuxvarOverapprox(operand);
			if (op == IASTUnaryExpression.op_minus && resultType.isIntegerType()) {
				addIntegerBoundsCheck(main, loc, result, resultType, op, hook, operand.mLrVal.getValue());
			}
			final Expression bwexpr =
					mExpressionTranslation.constructUnaryExpression(loc, op, operand.mLrVal.getValue(), resultType);
			final RValue rval = new RValue(bwexpr, resultType, false);
			result.mLrVal = rval;
			return result;
		default:
			throw new IllegalArgumentException("not a unary arithmetic operator " + op);
		}
	}

	@Override
	public BoogieTypeHelper getBoogieTypeHelper() {
		return mBoogieTypeHelper;
	}

	@Override
	public boolean isPreRunMode() {
		return mMainDispatcher instanceof PRDispatcher;
	}

	@Override
	public ProcedureManager getProcedureManager() {
		return mProcedureManager;
	}
}
