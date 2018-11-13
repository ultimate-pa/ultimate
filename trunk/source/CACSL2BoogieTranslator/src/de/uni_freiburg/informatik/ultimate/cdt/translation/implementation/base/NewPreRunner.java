/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.ASTVisitor;
import org.eclipse.cdt.core.dom.ast.IASTArrayDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTArraySubscriptExpression;
import org.eclipse.cdt.core.dom.ast.IASTCastExpression;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTFieldReference;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTName;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTParameterDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTPointerOperator;
import org.eclipse.cdt.core.dom.ast.IASTTypeId;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;
import org.eclipse.cdt.core.dom.ast.IBinding;
import org.eclipse.cdt.core.dom.ast.ICompositeType;
import org.eclipse.cdt.core.dom.ast.IField;
import org.eclipse.cdt.core.dom.ast.IFunction;
import org.eclipse.cdt.core.dom.ast.IType;
import org.eclipse.cdt.core.dom.ast.ITypedef;
import org.eclipse.cdt.core.dom.ast.IVariable;
import org.eclipse.cdt.core.dom.ast.c.ICBasicType;
import org.eclipse.cdt.internal.core.dom.parser.ITypeContainer;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTSimpleDeclaration;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStructOrUnion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStructOrUnion.StructOrUnion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;

/**
 * New PreRunner that determines variables on heap and function pointer ids based on {@link IBinding} and
 * {@link IASTName}
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class NewPreRunner extends ASTVisitor {

	/**
	 * The table containing all functions.
	 */
	private final Map<String, IASTNode> mFunctionTable;
	/**
	 * The table containing functions which are used as function pointers.
	 */
	private final LinkedHashMap<String, IASTDeclaration> mFunctionPointers;

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
	private final NameHandler mNameHandler;

	/**
	 * Constructor.
	 */
	public NewPreRunner(final FlatSymbolTable symTab, final Map<String, IASTNode> functionTable,
			final NameHandler nameHandler) {
		super();
		shouldVisitDeclarations = true;
		shouldVisitParameterDeclarations = true;
		shouldVisitExpressions = true;
		shouldVisitStatements = true;
		shouldVisitDeclSpecifiers = true;
		shouldVisitNames = true;

		mIsMMRequired = false;
		mSymTab = symTab;
		mFunctionTable = functionTable;
		mNameHandler = nameHandler;

		mFunctionPointers = new LinkedHashMap<>();
		mPointedToFunctionCounter = 0;
		mFunctionToIndex = new LinkedHashMap<>();
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
		return super.visit(declaration);
	}

	@Override
	public int visit(final IASTExpression expression) {
		if (expression instanceof IASTUnaryExpression) {
			final IASTUnaryExpression ue = (IASTUnaryExpression) expression;
			if (ue.getOperator() == IASTUnaryExpression.op_amper) {// every variable that is addressoffed has to be on
																	// the heap
				final IASTNode operand = ue.getOperand();
				// add the operand to VariablesOnHeap!
				String id = null;

				id = extractExpressionIdFromPossiblyComplexExpression(operand);

				mIsMMRequired = true;
				if (id != null) {
					// Rename the ID according to multiparse rules
					final String rslvId = mSymTab.applyMultiparseRenaming(expression.getContainingFilename(), id);
					final SymbolTableValue stv = mSymTab.findCSymbol(expression, rslvId);
					final IASTNode function = mFunctionTable.get(rslvId);
					if (function != null && stv == null) {
						// id is the name of a function
						// and not shadowed here
						updateFunctionPointers(rslvId, function);
						updateFunctionToIndex(rslvId);
					} else {
						moveSymbolOnHeap(expression, rslvId, stv);
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
			final SymbolTableValue stv = mSymTab.findCSymbol(expression, rslvId);
			if (function != null && stv == null
					&& !(expression.getParent() instanceof IASTFunctionCallExpression
							&& ((IASTFunctionCallExpression) expression.getParent()).getFunctionNameExpression()
									.equals(expression))) {
				updateFunctionPointers(rslvId, function);
				// functionPointers.put(id, function);
				updateFunctionToIndex(rslvId);
			}

			final IASTNode d = stv.getDeclarationNode();
			// don't check contains here!
			// if the identifier refers to an array and is used in a functioncall, the Array has to go on the heap
			if (d instanceof IASTArrayDeclarator && expression.getParent() instanceof IASTFunctionCallExpression) {
				moveSymbolOnHeap(expression, rslvId, stv);
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
			// is the operand an array?
			final IASTExpression operand = ((IASTCastExpression) expression).getOperand();
			final String operandId = extractExpressionIdFromPossiblyComplexExpression(operand);
			if (operandId != null) {
				final SymbolTableValue stv = mSymTab.findCSymbol(expression, operandId);
				final IASTNode stEntry = stv.getDeclarationNode();
				if (stEntry instanceof IASTArrayDeclarator) {
					final IASTTypeId tId = ((IASTCastExpression) expression).getTypeId();
					final IASTPointerOperator[] ptrOps = tId.getAbstractDeclarator().getPointerOperators();
					if (ptrOps != null && ptrOps.length >= 1) {
						moveSymbolOnHeap(expression, operandId, stv);
					}
				} else {
					// TODO: are there other cases?
				}
			} else {
				// TODO: treat other cases
			}
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
					if (nd.getPointerOperators() != null && nd.getPointerOperators().length != 0) {
						mIsMMRequired = true;
					}
					nd = nd.getNestedDeclarator();
				} while (nd != null);
			}

		}
		return super.visit(declaration);
	}

	@Override
	public int visit(final IASTName name) {

		final IBinding binding = name.resolveBinding();
		final String cName = mSymTab.applyMultiparseRenaming(name.getContainingFilename(), binding.getName());
		if (mSymTab.containsCSymbol(name, cName)) {
			return PROCESS_CONTINUE;
		}
		if (binding instanceof IVariable) {
			final CType cType = toCType(((IVariable) binding).getType());
			storeAsSymbol(name, cType, cName);
		} else if (binding instanceof IFunction) {

		} else if (binding instanceof ITypedef) {

		} else if (binding instanceof ICompositeType) {

		}
		return PROCESS_CONTINUE;
	}

	private CType toCType(final IType type) {
		if (type instanceof ICBasicType) {
			final ICBasicType basicType = (ICBasicType) type;
			switch (basicType.getKind()) {
			case eBoolean:
				return new CPrimitive(CPrimitives.BOOL);
			case eChar:
				if (basicType.isSigned()) {
					return new CPrimitive(CPrimitives.SCHAR);
				} else if (basicType.isUnsigned()) {
					return new CPrimitive(CPrimitives.UCHAR);
				} else {
					return new CPrimitive(CPrimitives.CHAR);
				}
			case eChar16:
				break;
			case eChar32:
				break;
			case eDecimal128:
				break;
			case eDecimal32:
				break;
			case eDecimal64:
				break;
			case eDouble:
				break;
			case eFloat:
				break;
			case eFloat128:
				break;
			case eInt:
				if (basicType.isUnsigned()) {
					return new CPrimitive(CPrimitives.UINT);
				}
				return new CPrimitive(CPrimitives.INT);
			case eInt128:
				break;
			case eNullPtr:
				break;
			case eUnspecified:
				break;
			case eVoid:
				return new CPrimitive(CPrimitives.VOID);
			case eWChar:
				break;
			default:
				break;

			}
		} else if (type instanceof ICompositeType) {
			final ICompositeType compType = ((ICompositeType) type);
			final StructOrUnion isStructOrUnion;
			if (compType.getKey() == ICompositeType.k_struct) {
				isStructOrUnion = StructOrUnion.STRUCT;
			} else if (compType.getKey() == ICompositeType.k_union) {
				isStructOrUnion = StructOrUnion.UNION;
			} else {
				throw new UnsupportedOperationException("Unknown ICompositeType key " + compType.getKey());
			}
			final int length = compType.getFields().length;
			final String[] fNames = new String[length];
			final CType[] fTypes = new CType[length];
			final List<Integer> bitFieldWidths = new ArrayList<>(length);
			for (int i = 0; i < length; ++i) {
				final IField field = compType.getFields()[i];
				fNames[i] = field.getName();
				fTypes[i] = toCType(field.getType());
				bitFieldWidths.add(-1);
				// if (node instanceof IASTFieldDeclarator) {
				// final IASTExpression expr = ((IASTFieldDeclarator) node).getBitFieldSize();
				// bitfieldSize = Integer.parseInt(expr.getRawSignature());
				// } else {
				// // we use -1 to indicate that this is no bitfield
				// bitfieldSize = -1;
				// }
			}
			return new CStructOrUnion(isStructOrUnion, compType.getName(), fNames, fTypes, bitFieldWidths);
		} else if (type instanceof ITypeContainer) {
			return toCType(((ITypeContainer) type).getType());
		}
		throw new UnsupportedOperationException("No transformation from IType " + type.getClass() + " to CType");
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
	private String extractExpressionIdFromPossiblyComplexExpression(final IASTNode expression) {
		if (expression instanceof IASTIdExpression) {
			final String id = ((IASTIdExpression) expression).getName().toString();
			return mSymTab.applyMultiparseRenaming(expression.getContainingFilename(), id);
		} else if (expression instanceof IASTFieldReference) {
			if (((IASTFieldReference) expression).isPointerDereference()) {
				return null; // "->" cancels out "&", like "*"
			}
			return extractExpressionIdFromPossiblyComplexExpression(((IASTFieldReference) expression).getFieldOwner());
		} else if (expression instanceof IASTArraySubscriptExpression) {
			return extractExpressionIdFromPossiblyComplexExpression(
					((IASTArraySubscriptExpression) expression).getArrayExpression());
		} else if (expression instanceof IASTUnaryExpression) {
			final int operator = ((IASTUnaryExpression) expression).getOperator();
			switch (operator) {
			case IASTUnaryExpression.op_star:
				return null; // the star and the amper cancel each other out here -> do nothing
			case IASTUnaryExpression.op_bracketedPrimary:
				return extractExpressionIdFromPossiblyComplexExpression(
						((IASTUnaryExpression) expression).getOperand());
			default:
				return null;
			}
		}
		return null;
	}

	private void updateFunctionToIndex(final String id) {
		if (!mFunctionToIndex.containsKey(id)) {
			mFunctionToIndex.put(id, mPointedToFunctionCounter++);
		}
	}

	private void moveSymbolOnHeap(final IASTNode hook, final String rslvId, final SymbolTableValue stv) {
		final CDeclaration cDec = stv.getCDecl();
		final IASTNode cursor = mSymTab.tableFindCursor(hook, rslvId, stv);
		final String boogieName = mNameHandler.getUniqueIdentifier(cursor, cDec.getName(), mSymTab.getCScopeId(cursor),
				true, cDec.getType());
		mSymTab.updateCSymbolFromCursor(cursor, rslvId, stv, stv.createOnHeap(boogieName));
	}

	private void storeAsSymbol(final IASTNode node, final CType cType, final String cName) {
		final CDeclaration cDec = new CDeclaration(cType, cName);
		final String boogieName = mNameHandler.getUniqueIdentifier(node, cDec.getName(), mSymTab.getCScopeId(node),
				false, cDec.getType());

		final DeclarationInformation dummyDeclInfo = DeclarationInformation.DECLARATIONINFO_GLOBAL;

		// this is only to have a minimal symbolTableEntry (containing boogieID) for translation of the initializer
		mSymTab.storeCSymbol(node, cDec.getName(),
				new SymbolTableValue(boogieName, null, cDec, dummyDeclInfo, node, false));
	}
}
