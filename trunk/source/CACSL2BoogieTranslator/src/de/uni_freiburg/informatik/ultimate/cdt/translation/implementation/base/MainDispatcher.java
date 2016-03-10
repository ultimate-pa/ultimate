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
/**
 * An example for a main dispatcher implementation.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.text.ParseException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map.Entry;

import org.apache.log4j.Logger;
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
import org.eclipse.cdt.core.dom.ast.IArrayType;
import org.eclipse.cdt.core.dom.ast.IBasicType;
import org.eclipse.cdt.core.dom.ast.IType;
import org.eclipse.cdt.core.dom.ast.ITypedef;
import org.eclipse.cdt.internal.core.dom.parser.IASTAmbiguousExpression;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTDesignatedInitializer;
import org.eclipse.cdt.internal.core.dom.parser.cpp.IASTAmbiguousCondition;

import de.uni_freiburg.informatik.ultimate.acsl.parser.Parser;
import de.uni_freiburg.informatik.ultimate.cdt.decorator.DecoratorNode;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionListResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
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
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.CACSL2BoogieBacktranslator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.WitnessInvariant;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.WitnessInvariants;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 04.01.2012
 */
public class MainDispatcher extends Dispatcher {
	/**
	 * The current decorator tree.
	 */
	private DecoratorNode decoratorTree;
	/**
	 * The iterator for the current decorator tree.
	 */
	private Iterator<DecoratorNode> decoratorTreeIterator;
	/**
	 * Temp variable for next ACSL calculation.
	 */
	private DecoratorNode nextACSLBuffer;
	/**
	 * Whether in the C program there is a variable that is declared as a pointer, and that is dereferenced at some
	 * point.
	 */
	private boolean thereAreDereferencedPointerVariables;

	LinkedHashSet<IASTDeclaration> reachableDeclarations;
	/**
	 * Variables that need some special memory handling.
	 */
	private LinkedHashSet<IASTNode> variablesOnHeap;

	// begin alex
	private LinkedHashSet<VariableDeclaration> _boogieDeclarationsOfVariablesOnHeap;
	private LinkedHashMap<Integer, String> indexToFunction;
	protected boolean m_BitvectorTranslation;
	protected WitnessInvariants m_WitnessInvariants;

	public LinkedHashMap<String, Integer> getFunctionToIndex() {
		return mFunctionToIndex;
	}

	public LinkedHashMap<Integer, String> getIndexToFunction() {
		return indexToFunction;
	}

	void addBoogieDeclarationOfVariableOnHeap(VariableDeclaration vd) {
		if (_boogieDeclarationsOfVariablesOnHeap == null)
			_boogieDeclarationsOfVariablesOnHeap = new LinkedHashSet<VariableDeclaration>();
		_boogieDeclarationsOfVariablesOnHeap.add(vd);
	}

	boolean getBoogieDeclarationsOfVariablesOnHeapContains(VariableDeclaration vd) {
		if (_boogieDeclarationsOfVariablesOnHeap == null)
			return false;
		return _boogieDeclarationsOfVariablesOnHeap.contains(vd);
	}

	// end alex

	public MainDispatcher(CACSL2BoogieBacktranslator backtranslator, WitnessInvariants witnessInvariants,
			IUltimateServiceProvider services, Logger logger) {
		super(backtranslator, services, logger);
		m_BitvectorTranslation = mPreferences.getBoolean(CACSLPreferenceInitializer.LABEL_BITVECTOR_TRANSLATION);
		m_WitnessInvariants = witnessInvariants;
	}

	/**
	 * Answers the question if we need the basic infrastructure for our memory model. That basic infrastructure is: the
	 * arrays "valid" and "length" and definitions of our malloc and deallocate functions, the type "$Pointer" and the
	 * NULL pointer. The basic infrastructure does not include the memory arrays themselves (like memory_int,...), those
	 * are triggered differently.
	 */
	@Override
	public boolean isMMRequired() {
		return !this.variablesOnHeap.isEmpty() || !this.mFunctionToIndex.isEmpty()
				|| this.thereAreDereferencedPointerVariables;
	}

	@Override
	public LinkedHashSet<IASTDeclaration> getReachableDeclarationsOrDeclarators() {
		return reachableDeclarations;
	}

	/**
	 * Returns a set of variables, that have to be handled using the memory model.
	 * 
	 * @return a set of variables, that have to be handled using the memory model.
	 */
	public LinkedHashSet<IASTNode> getVariablesForHeap() {
		return variablesOnHeap;
	}

	@Override
	protected void preRun(DecoratorNode node) {
		assert node.getCNode() != null;
		assert node.getCNode() instanceof IASTTranslationUnit;

		IASTTranslationUnit tu = (IASTTranslationUnit) node.getCNode();

		variablesOnHeap = new LinkedHashSet<>();

		FunctionTableBuilder ftb = new FunctionTableBuilder();
		tu.accept(ftb);
		PreRunner pr = new PreRunner(ftb.getFunctionTable());
		tu.accept(pr);

		variablesOnHeap.addAll(pr.getVarsForHeap());

		mFunctionToIndex = pr.getFunctionToIndex();

		boolean useDetNecessaryDeclarations = true;
		if (useDetNecessaryDeclarations) {
			DetermineNecessaryDeclarations dnd = new DetermineNecessaryDeclarations(this.getCheckedMethod(), this,
					ftb.getFunctionTable(), mFunctionToIndex);
			tu.accept(dnd);

			reachableDeclarations = dnd.getReachableDeclarationsOrDeclarators();
		} else {
			reachableDeclarations = null;
		}

		PRDispatcher prd = new PRDispatcher(backtranslator, mServices, mLogger, mFunctionToIndex,
				reachableDeclarations);
		prd.init();
		prd.dispatch(node);
		variablesOnHeap.addAll(prd.getVariablesOnHeap());

		indexToFunction = new LinkedHashMap<>();
		for (Entry<String, Integer> en : mFunctionToIndex.entrySet()) {
			indexToFunction.put(en.getValue(), en.getKey());
		}

		thereAreDereferencedPointerVariables = pr.isMMRequired();

	}

	@Override
	protected void init() {

		sideEffectHandler = new SideEffectHandler();
		typeHandler = new TypeHandler(!m_BitvectorTranslation);
		acslHandler = new ACSLHandler(m_WitnessInvariants != null);
		nameHandler = new NameHandler(backtranslator);
		cHandler = new CHandler(this, backtranslator, true, mLogger, typeHandler, m_BitvectorTranslation, nameHandler);
		this.backtranslator.setExpressionTranslation(((CHandler) cHandler).getExpressionTranslation());
		preprocessorHandler = new PreprocessorHandler();
		REPORT_WARNINGS = true;
	}

	@Override
	public Result dispatch(IASTNode n) {
		final List<AssertStatement> witnessInvariantsBefore;
		final String invariantBefore;
		if (m_WitnessInvariants != null) {
			WitnessInvariant wBefore = m_WitnessInvariants.getInvariantsBefore().get(n);
			invariantBefore = wBefore == null ? null : wBefore.getInvariant();
			witnessInvariantsBefore = translateWitnessInvariant(n, invariantBefore);
		} else {
			invariantBefore = null;
			witnessInvariantsBefore = Collections.emptyList();
		}

		final Result result;
		if (n instanceof IASTTranslationUnit) {
			result = cHandler.visit(this, ((IASTTranslationUnit) n));
		} else if (n instanceof IASTSimpleDeclaration) {
			result = cHandler.visit(this, (IASTSimpleDeclaration) n);
		} else if (n instanceof IASTParameterDeclaration) {
			result = cHandler.visit(this, (IASTParameterDeclaration) n);
		} else if (n instanceof IASTASMDeclaration) {
			result = cHandler.visit(this, (IASTASMDeclaration) n);
		} else if (n instanceof IASTDeclarator) {
			result = cHandler.visit(this, (IASTDeclarator) n);
		} else if (n instanceof IASTFunctionDefinition) {
			result = cHandler.visit(this, (IASTFunctionDefinition) n);
		} else if (n instanceof IASTArrayModifier) {
			result = cHandler.visit(this, (IASTArrayModifier) n);
		} else if (n instanceof IASTComment) {
			// TODO : remove? I think they are excluded by the parser anyway?
			result = cHandler.visit(this, (IASTComment) n);
		} else if (n instanceof IASTDeclaration) {
			result = cHandler.visit(this, (IASTDeclaration) n);
		} else if (n instanceof IASTDeclSpecifier) {
			// Here we decide which further Interface we want to visit, and
			// call the typeHandler
			if (n instanceof IASTSimpleDeclSpecifier) {
				result = typeHandler.visit(this, (IASTSimpleDeclSpecifier) n);
			} else if (n instanceof IASTNamedTypeSpecifier) {
				result = typeHandler.visit(this, (IASTNamedTypeSpecifier) n);
			} else if (n instanceof IASTEnumerationSpecifier) {
				result = typeHandler.visit(this, (IASTEnumerationSpecifier) n);
			} else if (n instanceof IASTElaboratedTypeSpecifier) {
				result = typeHandler.visit(this, (IASTElaboratedTypeSpecifier) n);
			} else if (n instanceof IASTCompositeTypeSpecifier) {
				result = typeHandler.visit(this, (IASTCompositeTypeSpecifier) n);
			} else {
				result = cHandler.visit(this, (IASTDeclSpecifier) n);
			}
		} else if (n instanceof IASTDeclarationListOwner) {
			// must be after IASTCompositeTypeSpecifier!
			result = cHandler.visit(this, (IASTDeclarationListOwner) n);
		} else if (n instanceof IASTStatement) {
			if (n instanceof IASTReturnStatement) {
				result = cHandler.visit(this, (IASTReturnStatement) n);
			} else if (n instanceof IASTSwitchStatement) {
				result = cHandler.visit(this, (IASTSwitchStatement) n);
			} else if (n instanceof IASTWhileStatement) {
				result = cHandler.visit(this, (IASTWhileStatement) n);
			} else if (n instanceof IASTLabelStatement) {
				result = cHandler.visit(this, (IASTLabelStatement) n);
			} else if (n instanceof IASTNullStatement) {
				result = cHandler.visit(this, (IASTNullStatement) n);
			} else if (n instanceof IASTContinueStatement) {
				result = cHandler.visit(this, (IASTContinueStatement) n);
			} else if (n instanceof IASTDeclarationStatement) {
				result = cHandler.visit(this, (IASTDeclarationStatement) n);
			} else if (n instanceof IASTDefaultStatement) {
				result = cHandler.visit(this, (IASTDefaultStatement) n);
			} else if (n instanceof IASTDoStatement) {
				result = cHandler.visit(this, (IASTDoStatement) n);
			} else if (n instanceof IASTExpressionStatement) {
				result = cHandler.visit(this, (IASTExpressionStatement) n);
			} else if (n instanceof IASTForStatement) {
				result = cHandler.visit(this, (IASTForStatement) n);
			} else if (n instanceof IASTGotoStatement) {
				result = cHandler.visit(this, (IASTGotoStatement) n);
			} else if (n instanceof IASTIfStatement) {
				result = cHandler.visit(this, (IASTIfStatement) n);
			} else if (n instanceof IASTCompoundStatement) {
				result = cHandler.visit(this, (IASTCompoundStatement) n);
			} else if (n instanceof IASTBreakStatement) {
				result = cHandler.visit(this, (IASTBreakStatement) n);
			} else if (n instanceof IASTCaseStatement) {
				result = cHandler.visit(this, (IASTCaseStatement) n);
			} else if (n instanceof IASTProblemStatement) {
				// error -> we will cancel the translation anyway ...
				// -> should be at the end of the parent if for performance
				result = cHandler.visit(this, (IASTProblemStatement) n);
			} else {
				result = cHandler.visit(this, (IASTStatement) n);
			}
		} else if (n instanceof IASTInitializer) {
			if (n instanceof IASTEqualsInitializer) {
				result = cHandler.visit(this, (IASTEqualsInitializer) n);
			} else if (n instanceof CASTDesignatedInitializer) {
				result = cHandler.visit(this, (CASTDesignatedInitializer) n);
			} else if (n instanceof IASTInitializerList) {
				result = cHandler.visit(this, (IASTInitializerList) n);
			} else {
				result = cHandler.visit(this, (IASTInitializer) n);
			}
		} else if (n instanceof IASTExpression) {
			if (n instanceof IASTLiteralExpression) {
				result = cHandler.visit(this, (IASTLiteralExpression) n);
			} else if (n instanceof IASTIdExpression) {
				result = cHandler.visit(this, (IASTIdExpression) n);
			} else if (n instanceof IASTFunctionCallExpression) {
				result = cHandler.visit(this, (IASTFunctionCallExpression) n);
			} else if (n instanceof IASTFieldReference) {
				result = cHandler.visit(this, (IASTFieldReference) n);
			} else if (n instanceof IASTExpressionList) {
				result = cHandler.visit(this, (IASTExpressionList) n);
			} else if (n instanceof IASTConditionalExpression) {
				result = cHandler.visit(this, (IASTConditionalExpression) n);
			} else if (n instanceof IASTCastExpression) {
				result = cHandler.visit(this, (IASTCastExpression) n);
			} else if (n instanceof IASTBinaryExpression) {
				result = cHandler.visit(this, (IASTBinaryExpression) n);
			} else if (n instanceof IASTBinaryTypeIdExpression) {
				result = cHandler.visit(this, (IASTBinaryTypeIdExpression) n);
			} else if (n instanceof IASTArraySubscriptExpression) {
				result = cHandler.visit(this, (IASTArraySubscriptExpression) n);
			} else if (n instanceof IASTAmbiguousExpression) {
				result = cHandler.visit(this, (IASTAmbiguousExpression) n);
			} else if (n instanceof IASTAmbiguousCondition) {
				result = cHandler.visit(this, (IASTAmbiguousCondition) n);
			} else if (n instanceof IASTTypeIdExpression) {
				result = cHandler.visit(this, (IASTTypeIdExpression) n);
			} else if (n instanceof IASTTypeIdInitializerExpression) {
				result = cHandler.visit(this, (IASTTypeIdInitializerExpression) n);
			} else if (n instanceof IASTUnaryExpression) {
				result = cHandler.visit(this, (IASTUnaryExpression) n);
			} else if (n instanceof IASTProblemExpression) {
				result = cHandler.visit(this, (IASTProblemExpression) n);
			} else {
				result = cHandler.visit(this, (IASTExpression) n);
			}
		} else if (n instanceof IASTFunctionStyleMacroParameter) {
			result = cHandler.visit(this, (IASTFunctionStyleMacroParameter) n);
		} else if (n instanceof IASTImplicitNameOwner) {
			result = cHandler.visit(this, (IASTImplicitNameOwner) n);
		} else if (n instanceof IASTName) {
			result = cHandler.visit(this, (IASTName) n);
		} else if (n instanceof IASTPointerOperator) {
			result = cHandler.visit(this, (IASTPointerOperator) n);
		} else if (n instanceof IASTPreprocessorMacroExpansion) {
			result = cHandler.visit(this, (IASTPreprocessorMacroExpansion) n);
		} else if (n instanceof IASTProblem) {
			result = cHandler.visit(this, (IASTProblem) n);
		} else if (n instanceof IASTTypeId) {
			result = cHandler.visit(this, (IASTTypeId) n);

			// Indirect implementations of IASTNode in CDT version 7:
		} else if (n instanceof IASTArrayDeclarator) {
			result = cHandler.visit(this, (IASTArrayDeclarator) n);
		} else if (n instanceof IASTASMDeclaration) {
			result = cHandler.visit(this, (IASTASMDeclaration) n);
		} else if (n instanceof IASTCompositeTypeSpecifier) {
			result = cHandler.visit(this, (IASTCompositeTypeSpecifier) n);
		} else if (n instanceof IASTFieldDeclarator) {
			result = cHandler.visit(this, (IASTFieldDeclarator) n);
		} else if (n instanceof IASTImplicitName) {
			result = cHandler.visit(this, (IASTImplicitName) n);
		} else if (n instanceof IASTInitializerClause) {
			result = cHandler.visit(this, (IASTInitializerClause) n);
		} else if (n instanceof IASTPointer) {
			result = cHandler.visit(this, (IASTPointer) n);
		} else if (n instanceof IASTPreprocessorMacroDefinition) {
			result = cHandler.visit(this, (IASTPreprocessorMacroDefinition) n);
		} else if (n instanceof IASTPreprocessorObjectStyleMacroDefinition) {
			result = cHandler.visit(this, (IASTPreprocessorObjectStyleMacroDefinition) n);
		} else if (n instanceof IASTStandardFunctionDeclarator) {
			result = cHandler.visit(this, (IASTStandardFunctionDeclarator) n);
		} else if (n instanceof IASTProblemDeclaration) {
			// error -> we will cancel the translation anyway ...
			// -> should be at the end of the parent if for performance
			result = cHandler.visit(this, (IASTProblemDeclaration) n);
		} else if (n instanceof IASTProblemTypeId) {
			// error -> we will cancel the translation anyway ...
			// -> should be at the end of the parent if for performance
			result = cHandler.visit(this, (IASTProblemTypeId) n);
		} else {
			String msg = "MainDispatcher: AST node type unknown: " + n.getClass();
			ILocation loc = LocationFactory.createCLocation(n);
			throw new UnsupportedSyntaxException(loc, msg);
		}
		final List<AssertStatement> witnessInvariantsAfter;
		final String invariantAfter;
		if (m_WitnessInvariants != null) {
			// TODO: Use the new information as you see fit
			WitnessInvariant wAfter = m_WitnessInvariants.getInvariantsAfter().get(n);
			invariantAfter = wAfter == null ? null : wAfter.getInvariant();
			witnessInvariantsAfter = translateWitnessInvariant(n, invariantAfter);
		} else {
			invariantAfter = null;
			witnessInvariantsAfter = Collections.emptyList();
		}

		if (!witnessInvariantsBefore.isEmpty() || !witnessInvariantsAfter.isEmpty()) {
			ILocation loc = LocationFactory.createCLocation(n);
			if (result instanceof ExpressionResult) {
				final ExpressionResult exprResult = (ExpressionResult) result;
				final ArrayList<Statement> stmt = exprResult.stmt;
				if (invariantBefore != null) {
					stmt.addAll(0, witnessInvariantsBefore);
					mLogger.warn("Checking witness invariant " + invariantBefore
							+ " directly before the following code " + loc);
				}
				if (invariantAfter != null) {
					stmt.addAll(witnessInvariantsAfter);
					mLogger.warn("Checking witness invariant " + invariantAfter + " directly after the following code "
							+ loc);
				}
			} else if (result instanceof ExpressionListResult) {
				ExpressionListResult exlire = (ExpressionListResult) result;
				if (invariantBefore != null) {
					ArrayList<Statement> stmt = exlire.list.get(0).stmt;
					stmt.addAll(0, witnessInvariantsBefore);
					mLogger.warn("Checking witness invariant " + invariantBefore
							+ " directly before the following code " + loc);
				}
				if (invariantAfter != null) {
					ArrayList<Statement> stmt = exlire.list.get(exlire.list.size() - 1).stmt;
					stmt.addAll(witnessInvariantsAfter);
					mLogger.warn("Checking witness invariant " + invariantAfter + " directly after the following code "
							+ loc);
				}
			} else {
				if (invariantBefore != null) {
					String message = "Found witness invariant but unable to add check " + invariantBefore
							+ " directly before the following code " + loc;
					mLogger.warn(message);
					// throw new AssertionError(message);
				}
				if (invariantAfter != null) {
					String message = "Found witness invariant but unable to add check " + invariantAfter
							+ " directly after the following code " + loc;
					mLogger.warn(message);
					// throw new AssertionError(message);
				}
			}
		}
		return result;
	}

	private List<AssertStatement> translateWitnessInvariant(IASTNode n, String invariant) throws AssertionError {
		// ILocation loca = LocationFactory.createCLocation(n);
		if (invariant != null) {
			ACSLNode acslNode = null;
			try {
				acslNode = Parser.parseComment("lstart\n assert " + invariant + ";", 0, 0, mLogger);
			} catch (Exception e) {
				throw new IllegalArgumentException(e);
			}
			Result translationResult = dispatch(acslNode);
			List<AssertStatement> invariants = new ArrayList<>();
			if (translationResult instanceof ExpressionResult) {
				ExpressionResult exprResult = (ExpressionResult) translationResult;
				if (!exprResult.auxVars.isEmpty()) {
					throw new AssertionError("must be translatable without auxvars");
				}
				if (!exprResult.decl.isEmpty()) {
					throw new AssertionError("must be translatable without new declarations");
				}
				if (!exprResult.overappr.isEmpty()) {
					throw new AssertionError("must be translatable without new overapproximations");
				}
				if (exprResult.stmt.size() > 1) {
					throw new AssertionError("must be translatable without additional statements");
				}
				Statement stmt = exprResult.stmt.get(0);
				if (stmt instanceof AssertStatement) {
					invariants.add((AssertStatement) stmt);
				} else {
					throw new AssertionError("must return one AssertStatement");
				}
			}
			return invariants;
		} else {
			return Collections.emptyList();
		}
	}

	@Override
	public Result dispatch(ACSLNode n) {
		if (n instanceof CodeAnnot) {
			return acslHandler.visit(this, (CodeAnnot) n);
		}
		if (n instanceof Expression) {
			if (n instanceof BinaryExpression) {
				return acslHandler.visit(this, (BinaryExpression) n);
			}
			if (n instanceof NotDefinedExpression) {
				return acslHandler.visit(this, (NotDefinedExpression) n);
			}
			if (n instanceof UnaryExpression) {
				return acslHandler.visit(this, (UnaryExpression) n);
			}
			if (n instanceof ArrayAccessExpression) {
				return acslHandler.visit(this, (ArrayAccessExpression) n);
			}
			if (n instanceof ArrayStoreExpression) {
				return acslHandler.visit(this, (ArrayStoreExpression) n);
			}
			if (n instanceof BitVectorAccessExpression) {
				return acslHandler.visit(this, (BitVectorAccessExpression) n);
			}
			if (n instanceof BooleanLiteral) {
				return acslHandler.visit(this, (BooleanLiteral) n);
			}
			if (n instanceof IntegerLiteral) {
				return acslHandler.visit(this, (IntegerLiteral) n);
			}
			if (n instanceof RealLiteral) {
				return acslHandler.visit(this, (RealLiteral) n);
			}
			if (n instanceof StringLiteral) {
				return acslHandler.visit(this, (StringLiteral) n);
			}
			if (n instanceof NullPointer) {
				return acslHandler.visit(this, (NullPointer) n);
			}
			if (n instanceof ValidExpression) {
				return acslHandler.visit(this, (ValidExpression) n);
			}
			if (n instanceof FreeableExpression) {
				return acslHandler.visit(this, (FreeableExpression) n);
			}
			if (n instanceof MallocableExpression) {
				return acslHandler.visit(this, (MallocableExpression) n);
			}
			if (n instanceof ACSLResultExpression) {
				return acslHandler.visit(this, (ACSLResultExpression) n);
			}
			if (n instanceof FieldAccessExpression) {
				return acslHandler.visit(this, (FieldAccessExpression) n);
			}
			if (n instanceof SizeOfExpression) {
				return acslHandler.visit(this, (SizeOfExpression) n);
			}
			if (n instanceof OldValueExpression) {
				return acslHandler.visit(this, (OldValueExpression) n);
			}
			if (n instanceof AtLabelExpression) {
				return acslHandler.visit(this, (AtLabelExpression) n);
			}
			if (n instanceof BaseAddrExpression) {
				return acslHandler.visit(this, (BaseAddrExpression) n);
			}
			if (n instanceof BlockLengthExpression) {
				return acslHandler.visit(this, (BlockLengthExpression) n);
			}
			if (n instanceof SyntacticNamingExpression) {
				return acslHandler.visit(this, (SyntacticNamingExpression) n);
			}
			if (n instanceof IdentifierExpression) {
				return acslHandler.visit(this, (IdentifierExpression) n);
			}
			if (n instanceof FunctionApplication) {
				return acslHandler.visit(this, (FunctionApplication) n);
			}
			if (n instanceof IfThenElseExpression) {
				return acslHandler.visit(this, (IfThenElseExpression) n);
			}
			if (n instanceof QuantifierExpression) {
				return acslHandler.visit(this, (QuantifierExpression) n);
			}
			if (n instanceof WildcardExpression) {
				return acslHandler.visit(this, (WildcardExpression) n);
			}
			return acslHandler.visit(this, (Expression) n);
		}
		if (n instanceof Contract) {
			return acslHandler.visit(this, (Contract) n);
		}
		if (n instanceof ContractStatement) {
			if (n instanceof Requires) {
				return acslHandler.visit(this, (Requires) n);
			}
			if (n instanceof Terminates) {
				return acslHandler.visit(this, (Terminates) n);
			}
			if (n instanceof Decreases) {
				return acslHandler.visit(this, (Decreases) n);
			}
			if (n instanceof Ensures) {
				return acslHandler.visit(this, (Ensures) n);
			}
			if (n instanceof Assigns) {
				return acslHandler.visit(this, (Assigns) n);
			}
			if (n instanceof Assumes) {
				return acslHandler.visit(this, (Assumes) n);
			}
			return acslHandler.visit(this, (ContractStatement) n);
		}
		if (n instanceof Completeness) {
			return acslHandler.visit(this, (Completeness) n);
		}
		if (n instanceof Behavior) {
			return acslHandler.visit(this, (Behavior) n);
		}
		if (n instanceof LogicStatement) {
			if (n instanceof Predicate) {
				return acslHandler.visit(this, (Predicate) n);
			}
			if (n instanceof LogicFunction) {
				return acslHandler.visit(this, (LogicFunction) n);
			}
			if (n instanceof Lemma) {
				return acslHandler.visit(this, (Lemma) n);
			}
			if (n instanceof Inductive) {
				return acslHandler.visit(this, (Inductive) n);
			}
			if (n instanceof Axiom) {
				return acslHandler.visit(this, (Axiom) n);
			}
			if (n instanceof Axiomatic) {
				return acslHandler.visit(this, (Axiomatic) n);
			}
			return acslHandler.visit(this, (LogicStatement) n);
		}
		if (n instanceof Invariant) {
			if (n instanceof GlobalInvariant) {
				return acslHandler.visit(this, (GlobalInvariant) n);
			}
			if (n instanceof GlobalLTLInvariant) {
				return acslHandler.visit(this, (GlobalLTLInvariant) n);
			}
			if (n instanceof TypeInvariant) {
				return acslHandler.visit(this, (TypeInvariant) n);
			}
			return acslHandler.visit(this, (Invariant) n);
		}
		if (n instanceof LoopStatement) {
			if (n instanceof LoopInvariant) {
				return acslHandler.visit(this, (LoopInvariant) n);
			}
			if (n instanceof LoopVariant) {
				return acslHandler.visit(this, (LoopVariant) n);
			}
			if (n instanceof LoopAssigns) {
				return acslHandler.visit(this, (LoopAssigns) n);
			}
			return acslHandler.visit(this, (LoopStatement) n);
		}
		if (n instanceof CodeStatement) {
			if (n instanceof Assertion) {
				return acslHandler.visit(this, (Assertion) n);
			}
			if (n instanceof CodeInvariant) {
				return acslHandler.visit(this, (CodeInvariant) n);
			}
			return acslHandler.visit(this, (CodeStatement) n);
		}
		if (n instanceof ACSLType) {
			return acslHandler.visit(this, (ACSLType) n);
		}
		if (n instanceof Case) {
			return acslHandler.visit(this, (Case) n);
		}
		if (n instanceof CodeForBehavior) {
			return acslHandler.visit(this, (CodeForBehavior) n);
		}
		if (n instanceof LoopAnnot) {
			return acslHandler.visit(this, (LoopAnnot) n);
		}
		if (n instanceof LoopForBehavior) {
			return acslHandler.visit(this, (LoopForBehavior) n);
		}
		if (n instanceof ModelVariable) {
			return acslHandler.visit(this, (ModelVariable) n);
		}
		if (n instanceof Parameter) {
			return acslHandler.visit(this, (Parameter) n);
		}
		if (n instanceof PolyIdentifier) {
			return acslHandler.visit(this, (PolyIdentifier) n);
		}
		if (n instanceof ACSLNode) {
			return acslHandler.visit(this, (ACSLNode) n);
		}
		String msg = "MainDispatcher: ACSL node type unknown: " + n.getClass();
		ILocation loc = LocationFactory.createACSLLocation(n);
		throw new UnsupportedSyntaxException(loc, msg);
	}

	@Override
	public Result dispatch(DecoratorNode node) {
		this.decoratorTree = node;
		this.decoratorTreeIterator = node.iterator();
		if (node.getCNode() != null) {
			return dispatch(node.getCNode());
		}
		return dispatch(node.getAcslNode());
	}

	@Override
	public NextACSL nextACSLStatement() throws ParseException {
		DecoratorNode current;
		if (nextACSLBuffer != null) {
			current = nextACSLBuffer;
			nextACSLBuffer = null;
		} else {
			if (!decoratorTreeIterator.hasNext()) {
				return null;
			}
			current = decoratorTreeIterator.next();
		}
		while (decoratorTreeIterator.hasNext() && current.getAcslNode() == null) {
			// jump over C nodes.
			current = decoratorTreeIterator.next();
		}
		if (!decoratorTreeIterator.hasNext() && current.getCNode() != null) {
			return null;
		}
		// current = found ACSL node
		ArrayList<ACSLNode> acsl = new ArrayList<ACSLNode>();
		checkACSLLocation(current);
		acsl.add(current.getAcslNode());
		if (!decoratorTreeIterator.hasNext()) {
			return new NextACSL(acsl, null);
		}
		// find successor C node with same parent as the found acsl node
		Iterator<DecoratorNode> myIterator = decoratorTree.iterator();
		DecoratorNode cNode = decoratorTree;
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

		DecoratorNode nextNode = decoratorTreeIterator.next();
		// block of ACSL nodes
		while (decoratorTreeIterator.hasNext() && nextNode.getCNode() == null) {
			// check parent of acsl nodes to be equivalent
			if (!current.getParent().getCNode().equals(nextNode.getParent().getCNode())) {
				// parent changed! not one block!
				assert nextACSLBuffer == null;
				if (nextNode.getAcslNode() != null) {
					nextACSLBuffer = nextNode;
				}
				return new NextACSL(acsl, successor);
			}
			checkACSLLocation(nextNode);
			acsl.add(nextNode.getAcslNode());
			nextNode = decoratorTreeIterator.next();
		}
		if (nextNode.getAcslNode() != null && current.getParent().getCNode().equals(nextNode.getParent().getCNode())) {
			acsl.add(nextNode.getAcslNode());
		} else if (nextNode.getAcslNode() != null) {
			nextACSLBuffer = nextNode;
		}
		nextAcsl = new NextACSL(acsl, successor);
		return new NextACSL(acsl, successor);
	}

	/**
	 * Parent node of an ACSL node should be a decorator node containing C. The C node should be instance of
	 * IASTCompoundStatement or IASTTranslationUnit.<br>
	 * <b>ACSL is unexpected in other locations.</b>
	 * 
	 * @param acslNode
	 *            the ACSL holding decorator node that should be checked.
	 */
	private static void checkACSLLocation(DecoratorNode acslNode) {
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
	public InferredType dispatch(IType type) {
		// All Known Subinterfaces:
		// IArrayType, IBasicType, ICArrayType, ICBasicType, ICompositeType,
		// ICPointerType, ICPPBasicType, ICPPClassSpecialization,
		// ICPPClassTemplate, ICPPClassTemplatePartialSpecialization,
		// ICPPClassTemplatePartialSpecializationSpecialization, ICPPClassType,
		// ICPPEnumeration, ICPPFunctionType, ICPPParameterPackType,
		// ICPPPointerToMemberType, ICPPReferenceType,
		// ICPPTemplateTemplateParameter, ICPPTemplateTypeParameter,
		// ICQualifierType, IEnumeration, IFunctionType, IGPPBasicType,
		// IGPPPointerToMemberType, IGPPPointerType, IGPPQualifierType,
		// IPointerType, IProblemBinding, IProblemType, IQualifierType, ITypedef
		if (type instanceof IBasicType) {
			return typeHandler.visit(this, (IBasicType) type);
		}
		if (type instanceof ITypedef) {
			return typeHandler.visit(this, (ITypedef) type);
		}
		if (type instanceof IArrayType) {
			return typeHandler.visit(this, (IArrayType) type);
		}
		return typeHandler.visit(this, type);
	}

	@Override
	public Result dispatch(IASTPreprocessorStatement n) {
		if (n instanceof IASTPreprocessorElifStatement) {
			return preprocessorHandler.visit(this, (IASTPreprocessorElifStatement) n);
		}
		if (n instanceof IASTPreprocessorElseStatement) {
			return preprocessorHandler.visit(this, (IASTPreprocessorElseStatement) n);
		}
		if (n instanceof IASTPreprocessorEndifStatement) {
			return preprocessorHandler.visit(this, (IASTPreprocessorEndifStatement) n);
		}
		if (n instanceof IASTPreprocessorErrorStatement) {
			return preprocessorHandler.visit(this, (IASTPreprocessorErrorStatement) n);
		}
		if (n instanceof IASTPreprocessorIfdefStatement) {
			return preprocessorHandler.visit(this, (IASTPreprocessorIfdefStatement) n);
		}
		if (n instanceof IASTPreprocessorIfndefStatement) {
			return preprocessorHandler.visit(this, (IASTPreprocessorIfndefStatement) n);
		}
		if (n instanceof IASTPreprocessorIfStatement) {
			return preprocessorHandler.visit(this, (IASTPreprocessorIfStatement) n);
		}
		if (n instanceof IASTPreprocessorIncludeStatement) {
			return preprocessorHandler.visit(this, (IASTPreprocessorIncludeStatement) n);
		}
		if (n instanceof IASTPreprocessorMacroDefinition) {
			return preprocessorHandler.visit(this, (IASTPreprocessorMacroDefinition) n);
		}
		if (n instanceof IASTPreprocessorPragmaStatement) {
			return preprocessorHandler.visit(this, (IASTPreprocessorPragmaStatement) n);
		}
		if (n instanceof IASTPreprocessorUndefStatement) {
			return preprocessorHandler.visit(this, (IASTPreprocessorUndefStatement) n);
		}
		return preprocessorHandler.visit(this, n);
	}
}
