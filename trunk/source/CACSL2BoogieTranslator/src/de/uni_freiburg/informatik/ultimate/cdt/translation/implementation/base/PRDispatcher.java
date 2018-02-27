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

import java.text.ParseException;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
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
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorMacroDefinition;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorMacroExpansion;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorObjectStyleMacroDefinition;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorStatement;
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
import org.eclipse.cdt.core.dom.ast.gnu.IGNUASTCompoundStatementExpression;
import org.eclipse.cdt.internal.core.dom.parser.IASTAmbiguousExpression;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTDesignatedInitializer;
import org.eclipse.cdt.internal.core.dom.parser.cpp.IASTAmbiguousCondition;

import cern.colt.Arrays;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieIdExtractor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.cdt.decorator.DecoratedUnit;
import de.uni_freiburg.informatik.ultimate.cdt.decorator.DecoratorNode;
import de.uni_freiburg.informatik.ultimate.cdt.parser.MultiparseSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.SkipResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.CACSL2BoogieBacktranslator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;

public class PRDispatcher extends Dispatcher {

	private final Set<IASTDeclaration> mReachableDeclarations;
	private final LinkedHashSet<IASTNode> mVariablesOnHeap;

	public PRDispatcher(final CACSL2BoogieBacktranslator backtranslator, final IUltimateServiceProvider services,
			final ILogger logger, final LinkedHashMap<String, Integer> functionToIndex,
			final Set<IASTDeclaration> reachableDeclarations, final LocationFactory locFac,
			final Map<String, IASTNode> functionTable, final MultiparseSymbolTable mst) {
		super(backtranslator, services, logger, locFac, functionTable, mst);
		mFunctionToIndex = functionToIndex;
		mReachableDeclarations = reachableDeclarations;
		mVariablesOnHeap = new LinkedHashSet<>();
	}

	/**
	 * Set variables that should be "on-Heap" in our implementation. For each such variable the set contains the
	 * IASTNode of the last variable declaration ("last" in case the variable has several declarations).
	 */
	public Set<IASTNode> getVariablesOnHeap() {
		return mVariablesOnHeap;
	}
	
	@Override
	protected void preRun(Collection<DecoratedUnit> nodes) {
		super.preRun(nodes);
	}

	@Override
	protected void init() {
		final boolean bitvectorTranslation =
				getPreferences().getBoolean(CACSLPreferenceInitializer.LABEL_BITVECTOR_TRANSLATION);
		final boolean overapproximateFloatingPointOperations =
				getPreferences().getBoolean(CACSLPreferenceInitializer.LABEL_OVERAPPROXIMATE_FLOATS);
		mTypeHandler = new TypeHandler(bitvectorTranslation);
		mCHandler = new CHandler(this, mBacktranslator, false, mLogger, mTypeHandler, bitvectorTranslation,
				overapproximateFloatingPointOperations, mNameHandler, mFlatTable);
	}

	@Override
	public Result dispatch(final Collection<DecoratedUnit> nodes) {
		// this.decoratorTree = node;
		// this.decoratorTreeIterator = node.iterator();
		return mCHandler.visit(this, nodes);
		// ACSL dispatch just returns null..
		// return dispatch(node.getAcslNode());
		// return null;
	}

	@Override
	public Result dispatch(final IASTNode n) {
		if (n instanceof IASTTranslationUnit) {
			return mCHandler.visit(this, ((IASTTranslationUnit) n));
		}
		if (n instanceof IASTSimpleDeclaration) {
			return mCHandler.visit(this, (IASTSimpleDeclaration) n);
		}
		if (n instanceof IASTParameterDeclaration) {
			return mCHandler.visit(this, (IASTParameterDeclaration) n);
		}
		if (n instanceof IASTASMDeclaration) {
			return mCHandler.visit(this, (IASTASMDeclaration) n);
		}
		if (n instanceof IASTDeclarator) {
			return mCHandler.visit(this, (IASTDeclarator) n);
		}
		if (n instanceof IASTFunctionDefinition) {
			return mCHandler.visit(this, (IASTFunctionDefinition) n);
		}
		if (n instanceof IASTArrayModifier) {
			return mCHandler.visit(this, n);
		}
		if (n instanceof IASTComment) {
			// TODO : remove? I think they are excluded by the parser anyway?
			return mCHandler.visit(this, n);
		}
		if (n instanceof IASTDeclaration) {
			return mCHandler.visit(this, n);
		}
		if (n instanceof IASTDeclSpecifier) {
			// Here we decide which further Interface we want to visit, and
			// call the typeHandler
			if (n instanceof IASTSimpleDeclSpecifier) {
				return mTypeHandler.visit(this, (IASTSimpleDeclSpecifier) n);
			}
			if (n instanceof IASTNamedTypeSpecifier) {
				return mTypeHandler.visit(this, (IASTNamedTypeSpecifier) n);
			}
			if (n instanceof IASTEnumerationSpecifier) {
				return mTypeHandler.visit(this, (IASTEnumerationSpecifier) n);
			}
			if (n instanceof IASTElaboratedTypeSpecifier) {
				return mTypeHandler.visit(this, (IASTElaboratedTypeSpecifier) n);
			}
			if (n instanceof IASTCompositeTypeSpecifier) {
				return mTypeHandler.visit(this, (IASTCompositeTypeSpecifier) n);
			}
			return mCHandler.visit(this, n);
		}
		if (n instanceof IASTDeclarationListOwner) {
			// must be after IASTCompositeTypeSpecifier!
			return mCHandler.visit(this, n);
		}
		if (n instanceof IASTStatement) {
			if (n instanceof IASTReturnStatement) {
				return mCHandler.visit(this, (IASTReturnStatement) n);
			}
			if (n instanceof IASTSwitchStatement) {
				return mCHandler.visit(this, (IASTSwitchStatement) n);
			}
			if (n instanceof IASTWhileStatement) {
				return mCHandler.visit(this, (IASTWhileStatement) n);
			}
			if (n instanceof IASTLabelStatement) {
				return mCHandler.visit(this, (IASTLabelStatement) n);
			}
			if (n instanceof IASTNullStatement) {
				return mCHandler.visit(this, (IASTNullStatement) n);
			}
			if (n instanceof IASTContinueStatement) {
				return mCHandler.visit(this, (IASTContinueStatement) n);
			}
			if (n instanceof IASTDeclarationStatement) {
				return mCHandler.visit(this, (IASTDeclarationStatement) n);
			}
			if (n instanceof IASTDefaultStatement) {
				return mCHandler.visit(this, (IASTDefaultStatement) n);
			}
			if (n instanceof IASTDoStatement) {
				return mCHandler.visit(this, (IASTDoStatement) n);
			}
			if (n instanceof IASTExpressionStatement) {
				return mCHandler.visit(this, (IASTExpressionStatement) n);
			}
			if (n instanceof IASTForStatement) {
				return mCHandler.visit(this, (IASTForStatement) n);
			}
			if (n instanceof IASTGotoStatement) {
				return mCHandler.visit(this, (IASTGotoStatement) n);
			}
			if (n instanceof IASTIfStatement) {
				return mCHandler.visit(this, (IASTIfStatement) n);
			}
			if (n instanceof IASTCompoundStatement) {
				return mCHandler.visit(this, (IASTCompoundStatement) n);
			}
			if (n instanceof IASTBreakStatement) {
				return mCHandler.visit(this, (IASTBreakStatement) n);
			}
			if (n instanceof IASTCaseStatement) {
				return mCHandler.visit(this, (IASTCaseStatement) n);
			}
			if (n instanceof IASTProblemStatement) {
				// error -> we will cancel the translation anyway ...
				// -> should be at the end of the parent if for performance
				return mCHandler.visit(this, (IASTProblemStatement) n);
			}
			return mCHandler.visit(this, n);
		}
		if (n instanceof IASTInitializer) {
			if (n instanceof IASTEqualsInitializer) {
				return mCHandler.visit(this, (IASTEqualsInitializer) n);
			}
			if (n instanceof CASTDesignatedInitializer) {
				return mCHandler.visit(this, (CASTDesignatedInitializer) n);
			}
			if (n instanceof IASTInitializerList) {
				return mCHandler.visit(this, (IASTInitializerList) n);
			}
			return mCHandler.visit(this, n);
		}
		if (n instanceof IASTExpression) {
			if (n instanceof IASTLiteralExpression) {
				return mCHandler.visit(this, (IASTLiteralExpression) n);
			}
			if (n instanceof IASTIdExpression) {
				return mCHandler.visit(this, (IASTIdExpression) n);
			}
			if (n instanceof IASTFunctionCallExpression) {
				return mCHandler.visit(this, (IASTFunctionCallExpression) n);
			}
			if (n instanceof IASTFieldReference) {
				return mCHandler.visit(this, (IASTFieldReference) n);
			}
			if (n instanceof IASTExpressionList) {
				return mCHandler.visit(this, (IASTExpressionList) n);
			}
			if (n instanceof IASTConditionalExpression) {
				return mCHandler.visit(this, (IASTConditionalExpression) n);
			}
			if (n instanceof IASTCastExpression) {
				return mCHandler.visit(this, (IASTCastExpression) n);
			}
			if (n instanceof IASTBinaryExpression) {
				return mCHandler.visit(this, (IASTBinaryExpression) n);
			}
			if (n instanceof IASTBinaryTypeIdExpression) {
				return mCHandler.visit(this, (IASTBinaryTypeIdExpression) n);
			}
			if (n instanceof IASTArraySubscriptExpression) {
				return mCHandler.visit(this, (IASTArraySubscriptExpression) n);
			}
			if (n instanceof IASTAmbiguousExpression) {
				return mCHandler.visit(this, (IASTAmbiguousExpression) n);
			}
			if (n instanceof IASTAmbiguousCondition) {
				return mCHandler.visit(this, (IASTAmbiguousCondition) n);
			}
			if (n instanceof IASTTypeIdExpression) {
				return mCHandler.visit(this, (IASTTypeIdExpression) n);
			}
			if (n instanceof IASTTypeIdInitializerExpression) {
				return mCHandler.visit(this, (IASTTypeIdInitializerExpression) n);
			}
			if (n instanceof IASTUnaryExpression) {
				return mCHandler.visit(this, (IASTUnaryExpression) n);
			}
			if (n instanceof IASTProblemExpression) {
				return mCHandler.visit(this, (IASTProblemExpression) n);
			}
			if (n instanceof IGNUASTCompoundStatementExpression) {
				return mCHandler.visit(this, (IGNUASTCompoundStatementExpression) n);
			}
			return mCHandler.visit(this, (IASTExpression) n);
		}
		if (n instanceof IASTFunctionStyleMacroParameter) {
			return mCHandler.visit(this, n);
		}
		if (n instanceof IASTImplicitNameOwner) {
			return mCHandler.visit(this, n);
		}
		if (n instanceof IASTName) {
			return mCHandler.visit(this, n);
		}
		if (n instanceof IASTPointerOperator) {
			return mCHandler.visit(this, n);
		}
		if (n instanceof IASTPreprocessorMacroExpansion) {
			return mCHandler.visit(this, n);
		}
		if (n instanceof IASTProblem) {
			return mCHandler.visit(this, (IASTProblem) n);
		}
		if (n instanceof IASTTypeId) {
			return mCHandler.visit(this, n);
		}
		// Indirect implementations of IASTNode in CDT version 7:
		if (n instanceof IASTArrayDeclarator) {
			return mCHandler.visit(this, (IASTArrayDeclarator) n);
		}
		if (n instanceof IASTASMDeclaration) {
			return mCHandler.visit(this, (IASTASMDeclaration) n);
		}
		if (n instanceof IASTCompositeTypeSpecifier) {
			return mCHandler.visit(this, n);
		}
		if (n instanceof IASTFieldDeclarator) {
			return mCHandler.visit(this, (IASTFieldDeclarator) n);
		}
		if (n instanceof IASTImplicitName) {
			return mCHandler.visit(this, n);
		}
		if (n instanceof IASTInitializerClause) {
			return mCHandler.visit(this, (IASTInitializerClause) n);
		}
		if (n instanceof IASTPointer) {
			return mCHandler.visit(this, (IASTPointer) n);
		}
		if (n instanceof IASTPreprocessorMacroDefinition) {
			return mCHandler.visit(this, n);
		}
		if (n instanceof IASTPreprocessorObjectStyleMacroDefinition) {
			return mCHandler.visit(this, n);
		}
		if (n instanceof IASTStandardFunctionDeclarator) {
			return mCHandler.visit(this, (IASTStandardFunctionDeclarator) n);
		}
		if (n instanceof IASTProblemDeclaration) {
			// error -> we will cancel the translation anyway ...
			// -> should be at the end of the parent if for performance
			return mCHandler.visit(this, (IASTProblemDeclaration) n);
		}
		if (n instanceof IASTProblemTypeId) {
			// error -> we will cancel the translation anyway ...
			// -> should be at the end of the parent if for performance
			return mCHandler.visit(this, (IASTProblemTypeId) n);
		}
		final String msg = "MainDispatcher: AST node type unknown: " + n.getClass();
		final ILocation loc = getLocationFactory().createCLocation(n);
		throw new UnsupportedSyntaxException(loc, msg);
	}

	@Override
	public Result dispatch(final IASTPreprocessorStatement node) {
		return new SkipResult();
	}
	
	@Override
	public Result dispatch(ACSLNode node) {
		// TODO Auto-generated method stub
		return null;
	}

//	@Override
//	public InferredType dispatch(final IType type) {
//		if (type instanceof IBasicType) {
//			return mTypeHandler.visit(this, (IBasicType) type);
//		}
//		if (type instanceof ITypedef) {
//			return mTypeHandler.visit(this, (ITypedef) type);
//		}
//		if (type instanceof IArrayType) {
//			return mTypeHandler.visit(this, (IArrayType) type);
//		}
//		return mTypeHandler.visit(this, type);
//	}

	@Override
	public Result dispatch(final ACSLNode node, final IASTNode cHook) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public NextACSL nextACSLStatement() throws ParseException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean isMMRequired() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isReachable(IASTDeclaration decl) {
		// Just mimic the main dispatcher.
		if (mReachableDeclarations == null) {
			return true;
		}
		// Temporary hack, dnd fails for auxvars.c regression test TODO wip/multi
		return true;
		// return mReachableDeclarations.contains(decl);
	}

	public void moveArrayAndStructIdsOnHeap(final ILocation loc, final Expression expr,
			final Set<AuxVarInfo> auxVars, final IASTNode hook) {
		final Set<String> auxVarIds = new HashSet<>();
//		for (final VariableDeclaration decl : auxVars.keySet()) {
		for (final AuxVarInfo auxvar : auxVars) {
//			final VariableDeclaration decl = auxvar.getVarDec();
//			for (final VarList varList : decl.getVariables()) {
//				for (final String id : varList.getIdentifiers()) {
//					auxVarIds.add(id);
//				}
//			}
			auxVarIds.add(auxvar.getExp().getIdentifier());
		}
		final BoogieIdExtractor bie = new BoogieIdExtractor();
		bie.processExpression(expr);
		for (final String id : bie.getIds()) {
			// auxVars do not have a corresponding C var, hence we move nothing
			// onto the heap
			if (!auxVarIds.contains(id)) {
				final FlatSymbolTable st = mCHandler.getSymbolTable();
				final String cid = st.getCIdForBoogieId(id);
				final SymbolTableValue value = st.findCSymbol(hook, cid);
				final CType type = value.getCVariable().getUnderlyingType();
				if (type instanceof CArray || type instanceof CStruct) {
					getVariablesOnHeap().add(value.getDeclarationNode());
				}
			}
		}
	}

	public void moveIdOnHeap(final ILocation loc, final IdentifierExpression idExpr, final IASTNode hook) {
		final String id = idExpr.getIdentifier();
		final FlatSymbolTable st = mCHandler.getSymbolTable();
		final String cid = st.getCIdForBoogieId(id);
		final SymbolTableValue value = st.findCSymbol(hook, cid);
		getVariablesOnHeap().add(value.getDeclarationNode());
	}
}
