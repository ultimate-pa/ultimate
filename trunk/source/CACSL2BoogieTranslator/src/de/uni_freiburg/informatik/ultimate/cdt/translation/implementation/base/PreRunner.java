/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
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

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.ASTVisitor;
import org.eclipse.cdt.core.dom.ast.IASTArrayDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTArraySubscriptExpression;
import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTCastExpression;
import org.eclipse.cdt.core.dom.ast.IASTCompositeTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTEqualsInitializer;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTFieldReference;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializer;
import org.eclipse.cdt.core.dom.ast.IASTInitializerList;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTParameterDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTPointerOperator;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IASTSwitchStatement;
import org.eclipse.cdt.core.dom.ast.IASTTypeId;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;
import org.eclipse.cdt.core.dom.ast.c.ICASTDesignatedInitializer;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTSimpleDeclaration;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.LinkedScopedHashMap;

/**
 * @authors Markus Lindenmann, Alexander Nutz
 * @date 12.12.2012
 */
public class PreRunner extends ASTVisitor {
	/**
	 * Variables, that have to go on the heap.
	 */
	private final LinkedHashSet<IASTNode> mVariablesOnHeap;
	/**
	 * The table containing all functions.
	 */
	private final Map<String, IASTNode> mFunctionTable;
	/**
	 * The table containing functions which are used as function pointers.
	 */
	private final LinkedHashMap<String, IASTDeclaration> mFunctionPointers;
	/**
	 * The symbol table during the translation.
	 */
	private final LinkedScopedHashMap<String, IASTNode> mTemporarySymbolTable;
	/**
	 * The symbol table used for renaming IDs according to multiparse rules.
	 */
	private final FlatSymbolTable mSymTab;
	/**
	 * Whether or not the memory model is required.
	 */
	private boolean mIsMMRequired;

	/**
	 * every function that is pointed to gets assigned an index -- its "address". This is the variable used for
	 * counting.
	 */
	private int mPointedToFunctionCounter;

	/**
	 * Every function that is pointed to gets assigned an index -- its "address". This mapping stores the association.
	 */
	private final LinkedHashMap<String, Integer> mFunctionToIndex;

	/**
	 * Constructor.
	 */
	public PreRunner(final FlatSymbolTable symTab, final Map<String, IASTNode> functionTable) {
		super();
		shouldVisitDeclarations = true;
		shouldVisitParameterDeclarations = true;
		shouldVisitExpressions = true;
		shouldVisitStatements = true;
		shouldVisitDeclSpecifiers = true;
		mSymTab = symTab;
		mIsMMRequired = false;
		mTemporarySymbolTable = new LinkedScopedHashMap<>();
		mVariablesOnHeap = new LinkedHashSet<>();
		mFunctionTable = functionTable;
		mFunctionPointers = new LinkedHashMap<>();
		mPointedToFunctionCounter = 0;
		mFunctionToIndex = new LinkedHashMap<>();
	}

	public PreRunnerResult getResult() {
		return new PreRunnerResult(mVariablesOnHeap, mFunctionToIndex, mIsMMRequired);
	}

	@Override
	public int visit(final IASTDeclSpecifier declSpec) {
		if (declSpec instanceof IASTCompositeTypeSpecifier) {
			mTemporarySymbolTable.beginScope();
		}
		return super.visit(declSpec);
	}

	@Override
	public int leave(final IASTDeclSpecifier declSpec) {
		if (declSpec instanceof IASTCompositeTypeSpecifier) {
			mTemporarySymbolTable.endScope();
		}
		return super.leave(declSpec);
	}

	@Override
	public int visit(final IASTParameterDeclaration declaration) {
		if (declaration.getDeclarator().getPointerOperators().length > 0) {
			mIsMMRequired = true;
		}
		if (declaration.getDeclarator() instanceof IASTArrayDeclarator) {
			mIsMMRequired = true;
		}
		if (declaration.getDeclarator() instanceof IASTFunctionDeclarator) {
			mIsMMRequired = true;
		}
		final String name = declaration.getDeclarator().getName().toString();
		mTemporarySymbolTable.put(name, declaration);
		return super.visit(declaration);
	}

	@Override
	public int visit(final IASTExpression expression) {
		if (expression instanceof IASTUnaryExpression) {
			// TODO 2017-05-08 Matthias: I changed this from createCLocation() to
			// createIgnoreCLocation(). If we really need line numbers here we
			// can pass a LocationFactory here.
			// final ILocation loc = LocationFactory.createCLocation(expression);
			final ILocation loc = LocationFactory.createIgnoreCLocation(expression);
			final IASTUnaryExpression ue = (IASTUnaryExpression) expression;
			if (ue.getOperator() == IASTUnaryExpression.op_amper) {
				// every variable that is addressoffed has to be on
				// the heap
				final IASTNode operand = ue.getOperand();
				// add the operand to VariablesOnHeap!
				String id = null;

				id = extraxtExpressionIdFromPossiblyComplexExpression(operand);

				mIsMMRequired = true;
				if (id != null) {
					// Rename the ID according to multiparse rules
					final String rslvId = mSymTab.applyMultiparseRenaming(expression.getContainingFilename(), id);
					final IASTNode function = mFunctionTable.get(rslvId);
					if (function != null && mTemporarySymbolTable.get(rslvId) == null) {
						// id is the name of a function
						// and not shadowed here
						updateFunctionPointers(rslvId, function);
						updateFunctionToIndex(rslvId);
					} else {
						mVariablesOnHeap.add(get(rslvId, loc));
					}
				}
			} else if (!mIsMMRequired && ue.getOperator() == IASTUnaryExpression.op_star) {
				mIsMMRequired = true;
			}
		} else if (expression instanceof IASTIdExpression) {
			final String id = ((IASTIdExpression) expression).getName().toString();
			final String rslvId = mSymTab.applyMultiparseRenaming(expression.getContainingFilename(), id);

			// a function address may be assigned to a function pointer without addressof
			// like fptr = f; where f is a function
			// check if id is the name of a function and not shadowed here
			final IASTNode function = mFunctionTable.get(rslvId);
			if (function != null && mTemporarySymbolTable.get(rslvId) == null
					&& !(expression.getParent() instanceof IASTFunctionCallExpression
							&& ((IASTFunctionCallExpression) expression.getParent()).getFunctionNameExpression()
									.equals(expression))) {
				updateFunctionPointers(rslvId, function);
				// functionPointers.put(id, function);
				updateFunctionToIndex(rslvId);
			}

			final IASTNode d = mTemporarySymbolTable.get(rslvId);
			// don't check contains here!
			// if the identifier refers to an array and is used in a functioncall, the Array has to go on the heap
			if (d instanceof IASTArrayDeclarator && expression.getParent() instanceof IASTFunctionCallExpression) {
				mVariablesOnHeap.add(d);
			}
		} else if (expression instanceof IASTFieldReference) {
			// TODO
			// if field is an array and there is no array sub expr!
		} else if (expression instanceof IASTFunctionCallExpression) {
			final IASTFunctionCallExpression fce = (IASTFunctionCallExpression) expression;
			final IASTExpression fne = fce.getFunctionNameExpression();
			if (fne instanceof IASTIdExpression) {
				final String name = ((IASTIdExpression) fne).getName().toString();
				if (name.equals("malloc")) {
					mIsMMRequired = true;
				} else if (name.equals("free")) {
					mIsMMRequired = true;
				}
			}
		} else if (expression instanceof IASTCastExpression) {
			// if we cast an array to a pointer, the array must be onHeap
			IASTNode toBePutOnHeap = null;

			// is the operand an array?
			boolean isArray = false;
			final IASTExpression operand = ((IASTCastExpression) expression).getOperand();
			final String operandId = extraxtExpressionIdFromPossiblyComplexExpression(operand);
			// if (operand instanceof IASTIdExpression) {
			if (operandId != null) {
				// IASTNode stEntry = sT.get(((IASTIdExpression) operand).getName().toString());
				final IASTNode stEntry = mTemporarySymbolTable.get(operandId);
				if (stEntry instanceof IASTArrayDeclarator) {
					isArray = true;
					toBePutOnHeap = stEntry;
				} else {
					// TODO: are there other cases?
				}
			} else {
				// TODO: treat other cases
			}

			// do we cast to a pointer?
			boolean castToPointer = false;
			if (isArray) {
				final IASTTypeId tId = ((IASTCastExpression) expression).getTypeId();
				final IASTPointerOperator[] ptrOps = tId.getAbstractDeclarator().getPointerOperators();
				if (ptrOps != null && ptrOps.length >= 1) {
					castToPointer = true;
				}
			}

			if (isArray && castToPointer) {
				mVariablesOnHeap.add(toBePutOnHeap);
			}

		} else if (expression instanceof IASTBinaryExpression) {
			final IASTBinaryExpression binEx = (IASTBinaryExpression) expression;
			if (binEx.getOperator() == IASTBinaryExpression.op_assign) {
				if (binEx.getOperand1() instanceof IASTIdExpression) {
					final String lId = ((IASTIdExpression) binEx.getOperand1()).getName().toString();
					final String rslvLeftId = mSymTab.applyMultiparseRenaming(binEx.getContainingFilename(), lId);
					final IASTNode lDecl = mTemporarySymbolTable.get(rslvLeftId);
					final String rId = extraxtExpressionIdFromPossiblyComplexExpression(binEx.getOperand2());
					final IASTNode rDecl = mTemporarySymbolTable.get(rId);
					if (lDecl instanceof IASTDeclarator) {
						if (((IASTDeclarator) lDecl).getPointerOperators() != null
								&& ((IASTDeclarator) lDecl).getPointerOperators().length > 0) {
							/*
							 * FIXME: why did we do this?? It leads to cp1 being put on the heap in case we have for
							 * example cp1 = cp2; where both are declared as char (or other) pointers --> this was not
							 * what I was aiming for when I wrote it, I suppose..
							 */
							// variablesOnHeap.add(rDecl);
						}

					}

				} else {
					// TODO: deal with array and struct access??
				}
			}
			// } else if (expression instanceof IASTLiteralExpression) {
			// // 2017-11-19 Matthias: This is a workaround that I introduced to
			// // make all variables that occur in statements of the form
			// // x = "someString"
			// // on-heap.
			// // It would probably be better to override some method
			// // (don't know which) that handles nodes for initialization
			// final IASTLiteralExpression litExpr = (IASTLiteralExpression) expression;
			// if (litExpr.getKind() == IASTLiteralExpression.lk_string_literal) {
			// if (litExpr.getParent() instanceof IASTInitializer) {
			// final IASTEqualsInitializer eqinit = getEqualsInitializer((IASTInitializer) litExpr.getParent());
			//
			// variablesOnHeap.add(eqinit.getParent());
			//
			//// if (eqinit.getParent() instanceof IASTArrayDeclarator) {
			//// final IASTArrayDeclarator arrayDecl = (IASTArrayDeclarator) eqinit.getParent();
			//// variablesOnHeap.add(arrayDecl);
			////
			//// }
			// }
			// }
		}
		return super.visit(expression);
	}

	@Override
	public int visit(final IASTDeclaration declaration) {
		if (declaration instanceof CASTSimpleDeclaration) {
			final CASTSimpleDeclaration cd = (CASTSimpleDeclaration) declaration;
			for (final IASTDeclarator d : cd.getDeclarators()) {
				IASTDeclarator nd = d;
				do {
					addNameOfNonFunctionDeclarator(nd);
					if (nd.getPointerOperators() != null && nd.getPointerOperators().length != 0) {
						mIsMMRequired = true;
					}
					nd = nd.getNestedDeclarator();

				} while (nd != null);

			}

		} else if (declaration instanceof IASTFunctionDefinition) {
			// IASTFunctionDefinition funDef = (IASTFunctionDefinition)declaration;
			// functionTable.put(funDef.getDeclarator().getName().toString(), funDef);
			mTemporarySymbolTable.beginScope();
		}
		return super.visit(declaration);
	}

	@Override
	public int leave(final IASTDeclaration declaration) {
		if (declaration instanceof IASTFunctionDefinition) {
			mTemporarySymbolTable.endScope();
		}
		return super.visit(declaration);
	}

	@Override
	public int visit(final IASTStatement statement) {
		if (statement instanceof IASTCompoundStatement && !(statement.getParent() instanceof IASTFunctionDefinition
				|| statement.getParent() instanceof IASTForStatement)) {
			mTemporarySymbolTable.beginScope();
		}
		if (statement instanceof IASTSwitchStatement) {
			mTemporarySymbolTable.beginScope();
		}
		if (statement instanceof IASTForStatement) {
			mTemporarySymbolTable.beginScope();
		}
		return super.visit(statement);
	}

	@Override
	public int leave(final IASTStatement statement) {
		if (statement instanceof IASTCompoundStatement && !(statement.getParent() instanceof IASTFunctionDefinition
				|| statement.getParent() instanceof IASTForStatement)) {
			// the scope for IASTFunctionDefinition and IASTForStatement was //FIXME what about while, do, ..?
			// opened in parent before!
			mTemporarySymbolTable.endScope();
		}
		if (statement instanceof IASTSwitchStatement) {
			mTemporarySymbolTable.endScope();
		}
		if (statement instanceof IASTForStatement) {
			mTemporarySymbolTable.endScope();
		}
		return super.leave(statement);
	}

	/**
	 * Starting from some initializer (must be one of IASTEqualsInitializer or IASTInitializerList or
	 * ICASTDesignatedInitializer) returns for the enclosing IASTEqualsInitializer.
	 *
	 * @param node
	 * @return
	 */
	private IASTEqualsInitializer getEqualsInitializer(final IASTInitializer node) {
		assert node instanceof IASTEqualsInitializer || node instanceof IASTInitializerList
				|| node instanceof ICASTDesignatedInitializer;
		if (node instanceof IASTEqualsInitializer) {
			return (IASTEqualsInitializer) node;
		}
		return getEqualsInitializer((IASTInitializer) node.getParent());
	}

	private void updateFunctionPointers(final String id, final IASTNode function) {
		if (function instanceof IASTFunctionDefinition) {
			mFunctionPointers.put(id, (IASTDeclaration) function);
		} else if (function instanceof IASTFunctionDeclarator) {
			mFunctionPointers.put(id, (IASTDeclaration) function.getParent());
		} else {
			assert false : "should not happen.. right?..";
		}
	}

	/**
	 * For an IdentifierExpression just return the identifier. For something like a struct access (s.a) return the
	 * identifier that designates the storage array used by the expression (here: s).
	 *
	 */
	private String extraxtExpressionIdFromPossiblyComplexExpression(final IASTNode expression) {
		if (expression instanceof IASTIdExpression) {
			final String id = ((IASTIdExpression) expression).getName().toString();
			return mSymTab.applyMultiparseRenaming(expression.getContainingFilename(), id);
		} else if (expression instanceof IASTFieldReference) {
			if (((IASTFieldReference) expression).isPointerDereference()) {
				return null; // "->" cancels out "&", like "*"
			}
			return extraxtExpressionIdFromPossiblyComplexExpression(((IASTFieldReference) expression).getFieldOwner());
		} else if (expression instanceof IASTArraySubscriptExpression) {
			return extraxtExpressionIdFromPossiblyComplexExpression(
					((IASTArraySubscriptExpression) expression).getArrayExpression());
		} else if (expression instanceof IASTUnaryExpression) {
			final int operator = ((IASTUnaryExpression) expression).getOperator();
			switch (operator) {
			case IASTUnaryExpression.op_star:
				return null; // the star and the amper cancel each other out here -> do nothing
			case IASTUnaryExpression.op_bracketedPrimary:
				return extraxtExpressionIdFromPossiblyComplexExpression(
						((IASTUnaryExpression) expression).getOperand());
			default:
				return null;
			}
		}
		return null;
	}

	private void addNameOfNonFunctionDeclarator(final IASTDeclarator d) {
		if (d instanceof IASTFunctionDeclarator) {
			// do nothing
		} else {
			final String key = d.getName().toString();
			final String rslvKey = mSymTab.applyMultiparseRenaming(d.getContainingFilename(), key);
			mTemporarySymbolTable.put(rslvKey, d);
		}
	}

	private void updateFunctionToIndex(final String id) {
		if (!mFunctionToIndex.containsKey(id)) {
			mFunctionToIndex.put(id, mPointedToFunctionCounter++);
		}
	}

	/**
	 * Getter to access the symbol table.
	 *
	 * @param n
	 *            the String name of the variable to retrieve from the symbol table.
	 * @param loc
	 *            the location for the error, if the String is not contained.
	 * @return the corresponding declaration for the given name.
	 */
	private IASTNode get(final String n, final ILocation loc) {
		if (!mTemporarySymbolTable.containsKey(n)) {
			final String msg = "PR: Missing declaration of " + n;
			throw new IncorrectSyntaxException(loc, msg);
		}
		return mTemporarySymbolTable.get(n);
	}

	public static final class PreRunnerResult {

		private final Set<IASTNode> mVariablesOnHeap;
		private final Map<String, Integer> mFunctionToIndex;
		private final boolean mHasDereferencedPointerVariables;

		public PreRunnerResult(final Set<IASTNode> variablesOnHeap, final Map<String, Integer> functionToIndex,
				final boolean hasDereferencedPointerVariables) {
			mVariablesOnHeap = variablesOnHeap;
			mFunctionToIndex = functionToIndex;
			mHasDereferencedPointerVariables = hasDereferencedPointerVariables;
		}

		public Set<IASTNode> getVariablesOnHeap() {
			return Collections.unmodifiableSet(mVariablesOnHeap);
		}

		public Map<String, Integer> getFunctionToIndex() {
			return Collections.unmodifiableMap(mFunctionToIndex);
		}

		public boolean isHasDereferencedPointerVariables() {
			return mHasDereferencedPointerVariables;
		}
	}

}
