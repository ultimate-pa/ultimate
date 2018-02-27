/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
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
 * An example of a Type-Handler implementation.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.IASTCompositeTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTElaboratedTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTEnumerationSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTEnumerationSpecifier.IASTEnumerator;
import org.eclipse.cdt.core.dom.ast.IASTNamedTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclSpecifier;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTTypedefNameSpecifier;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieStructType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CNamed;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.DeclarationResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.DeclaratorResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.SkipResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.TypesResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.BoogieASTUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ICHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.util.datastructures.LinkedScopedHashMap;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.SymmetricHashRelation;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 07.02.2012
 * @author Alexander Nutz
 */
public class TypeHandler implements ITypeHandler {
	/**
	 * Maps the cIdentifier of a struct, enumeration, or union (when this is implemented) to the ResultType that
	 * represents this type at the moment
	 */
	private final LinkedScopedHashMap<String, TypesResult> mDefinedTypes;
	/**
	 * Undefined struct types.
	 */
	private final LinkedHashSet<String> mIncompleteType;
	/**
	 * counting levels of struct declaration.
	 */
	private int mStructCounter;

	/**
	 * Contains all primitive types that occurred in program.
	 */
	private final Set<CPrimitive.CPrimitives> mOccurredPrimitiveTypes = new HashSet<>();

	/**
	 * if false we translate CPrimitives whose general type is INT to int. If true we translate CPrimitives whose
	 * general type is INT to identically named types,
	 */
	private final boolean mBitvectorTranslation;

	/**
	 * States if an ASTNode for the pointer type was constructed and hence this type has to be declared.
	 */
	private boolean mPointerTypeNeeded = false;

	/**
	 * Is true iff we yet processed a floating type. (And hence floating types have to be added to Boogie).
	 */
	private boolean mFloatingTypesNeeded = false;
	private ICHandler mCHandler;

	private final BoogieType mBoogiePointerType;

	public Set<CPrimitive.CPrimitives> getOccurredPrimitiveTypes() {
		return mOccurredPrimitiveTypes;
	}

	public boolean isBitvectorTranslation() {
		return mBitvectorTranslation;
	}

	/**
	 * Constructor.
	 *
	 * @param useIntForAllIntegerTypes
	 */
	public TypeHandler(final boolean bitvectorTranslation) {
		mBitvectorTranslation = bitvectorTranslation;
		mDefinedTypes = new LinkedScopedHashMap<>();
		mIncompleteType = new LinkedHashSet<>();
		mBoogiePointerType = new BoogieStructType(
				new String[] { SFO.POINTER_BASE, SFO.POINTER_OFFSET },
				new BoogieType[] { BoogieType.TYPE_INT, BoogieType.TYPE_INT });
	}

	@Override
	public boolean isStructDeclaration() {
		assert mStructCounter >= 0;
		return mStructCounter != 0;
	}

	@Override
	public Result visit(final Dispatcher main, final IASTNode node) {
		final String msg = "TypeHandler: Not yet implemented: " + node.toString();
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		throw new UnsupportedSyntaxException(loc, msg);
	}

	/**
	 * @deprecated is not supported in this handler! Do not use!
	 */
	@Deprecated
	@Override
	public Result visit(final Dispatcher main, final ACSLNode node) {
		throw new UnsupportedOperationException("Implementation Error: use ACSL handler for " + node.getClass());
	}

	@Override
	public Result visit(final Dispatcher main, final IASTSimpleDeclSpecifier node) {
		// we have model.boogie.ast.PrimitiveType, which should
		// only contain BOOL, INT, REAL ...
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		switch (node.getType()) {
		case IASTSimpleDeclSpecifier.t_void: {
			// there is no void in Boogie,
			// so we simply have no result variable.
			final CPrimitive cvar = new CPrimitive(node);
			return (new TypesResult(null, false, true, cvar));
		}
		case IASTSimpleDeclSpecifier.t_unspecified: {
			final String msg = "unspecified type, defaulting to int";
			main.warn(loc, msg);
		}
		case IASTSimpleDeclSpecifier.t_bool:
		case IASTSimpleDeclSpecifier.t_char:
		case IASTSimpleDeclSpecifier.t_int: {
			// so int is also a primitive type
			// NOTE: in a extended implementation we should
			// handle here different types of int (short, long,...)
			final CPrimitive cvar = new CPrimitive(node);
			return (new TypesResult(cPrimitive2AstType(loc, cvar), node.isConst(), false, cvar));
		}
		case IASTSimpleDeclSpecifier.t_double:
		case IASTSimpleDeclSpecifier.t_float: {
			// floating point number are not supported by Ultimate,
			// somehow we treat it here as REALs
			final CPrimitive cvar = new CPrimitive(node);
			return (new TypesResult(new PrimitiveType(loc, SFO.REAL), node.isConst(), false, cvar));
		}
		case IASTSimpleDeclSpecifier.t_typeof: {
			/*
			 * https://gcc.gnu.org/onlinedocs/gcc/Typeof.html : The syntax of using of this keyword looks like sizeof,
			 * but the construct acts semantically like a type name defined with typedef. There are two ways of writing
			 * the argument to typeof: with an expression or with a type. Here is an example with an expression: typeof
			 * (x[0](1)) This assumes that x is an array of pointers to functions; the type described is that of the
			 * values of the functions. Here is an example with a typename as the argument: typeof (int *) Here the type
			 * described is that of pointers to int.
			 */
			final Result opRes = main.dispatch(node.getDeclTypeExpression());
			if (opRes instanceof ExpressionResult) {
				final CType cType = ((ExpressionResult) opRes).mLrVal.getCType();
				return new TypesResult(cType2AstType(loc, cType), node.isConst(), false, cType);
			} else if (opRes instanceof DeclaratorResult) {
				final CType cType = ((DeclaratorResult) opRes).getDeclaration().getType();
				return new TypesResult(cType2AstType(loc, cType), node.isConst(), false, cType);
			}
		}
		default:
			// long, long long, and short are the same as int, iff there are
			// no restrictions / asserts in boogie
			if (node.isLongLong() || node.isLong() || node.isShort() || node.isUnsigned()) {
				final CPrimitive cvar = new CPrimitive(node);
				return (new TypesResult(new PrimitiveType(loc, SFO.INT), node.isConst(), false, cvar));
			}
			// if we do not find a type we cancel with Exception
			final String msg = "TypeHandler: We do not support this type!" + node.getType();
			throw new UnsupportedSyntaxException(loc, msg);
		}
	}

	@Override
	public Result visit(final Dispatcher main, final IASTNamedTypeSpecifier node) {
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		if (node instanceof CASTTypedefNameSpecifier) {
			final String cId = node.getName().toString();

			// quick solution --> TODO: maybe make this dependent on includes,
			// maybe be more elegant (make an entry to symboltable, make a typedef in boogie file??)
			if (cId.equals("size_t") || cId.equals("ssize_t")) {
				return (new TypesResult(new PrimitiveType(loc, SFO.REAL), node.isConst(), false,
						new CPrimitive(CPrimitives.UINT)));
			} else if (cId.equals("__builtin_va_list")) {
				return (new TypesResult(constructPointerType(loc), node.isConst(), false,
						new CPointer(new CPrimitive(CPrimitives.CHAR))));
			} else if (cId.equals("__pthread_list_t")) {
				return (new TypesResult(constructPointerType(loc), node.isConst(), false,
						new CPointer(new CPrimitive(CPrimitives.VOID))));
			} else {
				final String modifiedName = 
						main.mCHandler.getSymbolTable().applyMultiparseRenaming(node.getContainingFilename(), cId);
				final String bId = main.mCHandler.getSymbolTable().findCSymbol(node, modifiedName).getBoogieName();
				return new TypesResult(new NamedType(loc, bId, null), false, false, 
						main.mCHandler.getSymbolTable().findCSymbol(node, modifiedName).getCDecl().getType());
				// return new TypesResult(new NamedType(loc, bId, null), false, false, // TODO: replace constants
				//  		new CNamed(bId, mDefinedTypes.get(bId).cType));
			}
		}
		final String msg = "Unknown or unsupported type! " + node.toString();
		throw new UnsupportedSyntaxException(loc, msg);
	}

	@Override
	public Result visit(final Dispatcher main, final IASTEnumerationSpecifier node) {
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		final String cId = node.getName().toString();
		final String rslvName = 
				main.mCHandler.getSymbolTable().applyMultiparseRenaming(node.getContainingFilename(), cId);
		// values of enum have type int
		final CPrimitive intType = new CPrimitive(CPrimitives.INT);
		final String enumId = main.mNameHandler.getUniqueIdentifier(node, node.getName().toString(),
				main.mCHandler.getSymbolTable().getCScopeId(node), false, intType);
		final int nrFields = node.getEnumerators().length;
		final String[] fNames = new String[nrFields];
		final Expression[] fValues = new Expression[nrFields];
		for (int i = 0; i < nrFields; i++) {
			final IASTEnumerator e = node.getEnumerators()[i];
			fNames[i] = e.getName().toString();
			if (e.getValue() != null) {
				final ExpressionResult rex = (ExpressionResult) main.dispatch(e.getValue());
				fValues[i] = rex.mLrVal.getValue();
				// assert (fValues[i] instanceof IntegerLiteral) ||
				// (fValues[i] instanceof BitvecLiteral) :
				// "assuming that only IntegerLiterals or BitvecLiterals can occur while translating an enum constant";
			} else {
				fValues[i] = null;
			}
		}
		final CEnum cEnum = new CEnum(enumId, fNames, fValues);
		final ASTType at = cPrimitive2AstType(loc, intType);
		final TypesResult result = new TypesResult(at, false, false, cEnum);

		final String incompleteTypeName = "ENUM~" + rslvName;
		if (mIncompleteType.contains(incompleteTypeName)) {
			mIncompleteType.remove(incompleteTypeName);
			final TypesResult incompleteType = mDefinedTypes.get(rslvName);
			final CEnum incompleteEnum = (CEnum) incompleteType.cType;
			// search for any typedefs that were made for the incomplete type
			// typedefs are made globally, so the CHandler has to do this
			((CHandler) main.mCHandler).completeTypeDeclaration(incompleteEnum, cEnum);

			incompleteEnum.complete(cEnum);
		}

		if (!enumId.equals(SFO.EMPTY)) {
			mDefinedTypes.put(rslvName, result);
		}

		return result;
	}

	@Override
	public Result visit(final Dispatcher main, final IASTElaboratedTypeSpecifier node) {
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		if (node.getKind() == IASTElaboratedTypeSpecifier.k_struct
				|| node.getKind() == IASTElaboratedTypeSpecifier.k_enum
				|| node.getKind() == IASTElaboratedTypeSpecifier.k_union) {
			final String type = node.getName().toString();
			final String rslvName = 
					main.mCHandler.getSymbolTable().applyMultiparseRenaming(node.getContainingFilename(), type);

			// if (mDefinedTypes.containsKey(type)) {
			final TypesResult originalType = mDefinedTypes.get(rslvName);
			// if (originalType == null && node.getKind() == IASTElaboratedTypeSpecifier.k_enum)
			// // --> we have an incomplete enum --> do nothing
			// //(i cannot think of an effect of an incomplete enum declaration right now..)
			// return new ResultSkip();
			if (originalType != null) {
				// --> we have a normal struct, union or enum declaration
				final TypesResult withoutBoogieTypedef = new TypesResult(originalType.getType(), originalType.isConst,
						originalType.isVoid, originalType.cType);
				return withoutBoogieTypedef;
			}
			// --> This is a definition of an incomplete struct, enum or union.
			String incompleteTypeName;
			if (node.getKind() == IASTElaboratedTypeSpecifier.k_struct) {
				incompleteTypeName = "STRUCT~" + type;
			} else if (node.getKind() == IASTElaboratedTypeSpecifier.k_union) {
				incompleteTypeName = "UNION~" + type;
			} else {
				incompleteTypeName = "ENUM~" + type;
			}

			mIncompleteType.add(incompleteTypeName);
			// FIXME : not sure, if null is a good idea!
			// ResultTypes r = new ResultTypes(new NamedType(loc, name,
			// new ASTType[0]), false, false, null);
			CType ctype;
			if (node.getKind() == IASTElaboratedTypeSpecifier.k_struct) {
				ctype = new CStruct(type);
			} else if (node.getKind() == IASTElaboratedTypeSpecifier.k_union) {
				ctype = new CUnion(type);
			} else {
				ctype = new CEnum(type);
			}
			final TypesResult r =
					new TypesResult(new NamedType(loc, incompleteTypeName, new ASTType[0]), false, false, ctype);

			mDefinedTypes.put(rslvName, r);

			return r;
		}
		final String msg = "Not yet implemented: Spec [" + node.getKind() + "] of " + node.getClass();
		throw new UnsupportedSyntaxException(loc, msg);
	}

	@Override
	public Result visit(final Dispatcher main, final IASTCompositeTypeSpecifier node) {
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		@Deprecated // 2016-12-08 Matthias: it seems like field is never used.
		final ArrayList<VarList> fields = new ArrayList<>();
		// TODO : include inactives? what are inactives?
		final ArrayList<String> fNames = new ArrayList<>();
		final ArrayList<CType> fTypes = new ArrayList<>();
		final ArrayList<Integer> bitFieldWidths = new ArrayList<>();
		mStructCounter++;
		for (final IASTDeclaration dec : node.getDeclarations(false)) {
			final Result r = main.dispatch(dec);
			if (r instanceof DeclarationResult) {
				final DeclarationResult rdec = (DeclarationResult) r;
				for (final CDeclaration declaration : rdec.getDeclarations()) {
					fNames.add(declaration.getName());
					fTypes.add(declaration.getType());
					fields.add(new VarList(loc, new String[] { declaration.getName() },
							cType2AstType(loc, declaration.getType())));
					if (main.getPreferences().getBoolean(CACSLPreferenceInitializer.LABEL_BITPRECISE_BITFIELDS)) {
						if (declaration.getBitfieldSize() != -1) {
							final String msg = "bitfield implementation not yet bitprecisse (soundness first)";
							throw new UnsupportedSyntaxException(loc, msg);
						}
					}
					bitFieldWidths.add(declaration.getBitfieldSize());
				}
			} else if (r instanceof SkipResult) { // skip ;)
			} else {
				final String msg = "Unexpected syntax in struct declaration!";
				throw new UnsupportedSyntaxException(loc, msg);
			}
		}
		mStructCounter--;

		final String cId = node.getName().toString();
		final String rslvName = 
				main.mCHandler.getSymbolTable().applyMultiparseRenaming(node.getContainingFilename(), cId);

		CStruct cvar;
		String name = null;
		if (node.getKey() == IASTCompositeTypeSpecifier.k_struct) {
			name = "STRUCT~" + rslvName;
			cvar = new CStruct(fNames.toArray(new String[fNames.size()]), fTypes.toArray(new CType[fTypes.size()]),
					bitFieldWidths);
		} else if (node.getKey() == IASTCompositeTypeSpecifier.k_union) {
			name = "UNION~" + rslvName;
			cvar = new CUnion(fNames.toArray(new String[fNames.size()]), fTypes.toArray(new CType[fTypes.size()]),
					bitFieldWidths);
		} else {
			throw new UnsupportedOperationException();
		}

		final NamedType namedType = new NamedType(loc, name, new ASTType[0]);
		final ASTType type = namedType;
		final TypesResult result = new TypesResult(type, false, false, cvar);

		if (mIncompleteType.contains(name)) {
			mIncompleteType.remove(name);
			final TypesResult incompleteType = mDefinedTypes.get(rslvName);
			final CStruct incompleteStruct = (CStruct) incompleteType.cType;
			// search for any typedefs that were made for the incomplete type
			// typedefs are made globally, so the CHandler has to do this
			((CHandler) main.mCHandler).completeTypeDeclaration(incompleteStruct, cvar);

			incompleteStruct.complete(cvar);
		}

		if (!cId.equals(SFO.EMPTY)) {
			mDefinedTypes.put(rslvName, result);
		}
		return result;
	}

//	@Override
//	public InferredType visit(final Dispatcher main, final org.eclipse.cdt.core.dom.ast.IType type) {
//		if (type instanceof CPointerType) {
//			return new InferredType(Type.Pointer);
//		}
//		// Handle the generic case of IType, if the specific case is not yet
//		// implemented
//		final String msg = "TypeHandler: Not yet implemented: " + type.getClass().toString();
//		// TODO : no idea what location should be set to ...
//		main.unsupportedSyntax(null, msg);
//		return new InferredType(Type.Unknown);
//	}
//
//	@Override
//	public InferredType visit(final Dispatcher main, final ITypedef type) {
//		assert false : "I don't think this should still be used";
//		if (!mDefinedTypes.containsKey(type.getName())) {
//			final String msg = "Unknown C typedef: " + type.getName();
//			// TODO : no idea what location should be set to ...
//			throw new IncorrectSyntaxException(null, msg);
//		}
//		return new InferredType(mDefinedTypes.get(type.getName()).getType());
//	}
//
//	@Override
//	public InferredType visit(final Dispatcher main, final IBasicType type) {
//		switch (type.getKind()) {
//		case eBoolean:
//			return new InferredType(Type.Boolean);
//		case eChar:
//		case eChar16:
//		case eChar32:
//		case eInt:
//			return new InferredType(Type.Integer);
//		case eDouble:
//		case eFloat:
//			return new InferredType(Type.Real);
//		case eWChar: // TODO : verify! Not sure what WChar means!
//			return new InferredType(Type.String);
//		case eVoid:
//			return new InferredType(Type.Void);
//		case eUnspecified:
//		default:
//			return new InferredType(Type.Unknown);
//		}
//	}

	@Override
	public ASTType getTypeOfStructLHS(final FlatSymbolTable sT, final ILocation loc, final StructLHS lhs,
			final IASTNode hook) {
		final String[] flat = BoogieASTUtil.getLHSList(lhs);
		final String leftMostId = flat[0];
		assert leftMostId.equals(BoogieASTUtil.getLHSId(lhs));
		assert sT.containsBoogieSymbol(leftMostId);
		final String cId = sT.getCIdForBoogieId(leftMostId);
		assert sT.containsCSymbol(hook, cId);
		final ASTType t = cType2AstType(loc, sT.findCSymbol(hook, cId).getCVariable());
		return traverseForType(loc, t, flat, 1);
	}

	/**
	 * Returns the type of the field in the struct.
	 *
	 * @param loc
	 *            the location, where errors should be set, if there are any!
	 * @param t
	 *            the type to process.
	 * @param flat
	 *            the flattend LHS.
	 * @param i
	 *            index in flat[].
	 * @return the type of the field.
	 */
	private static ASTType traverseForType(final ILocation loc, final ASTType t, final String[] flat, final int i) {
		assert i > 0 && i <= flat.length;
		if (i >= flat.length) {
			return t;
		}
		if (t instanceof ArrayType) {
			return traverseForType(loc, ((ArrayType) t).getValueType(), flat, i);
		}
		if (t instanceof StructType) {
			for (final VarList vl : ((StructType) t).getFields()) {
				assert vl.getIdentifiers().length == 1;
				// should hold by construction!
				if (vl.getIdentifiers()[0].equals(flat[i])) {
					// found the field!
					return traverseForType(loc, vl.getType(), flat, i + 1);
				}
			}
			final String msg = "Field '" + flat[i] + "' not found in " + t;
			throw new IncorrectSyntaxException(loc, msg);
		}
		final String msg = "Something went wrong while determining types!";
		throw new UnsupportedSyntaxException(loc, msg);
	}

//	@Override
//	public InferredType visit(final Dispatcher main, final IArrayType type) {
//		return main.dispatch(type.getType());
//	}

	@Override
	public LinkedScopedHashMap<String, TypesResult> getDefinedTypes() {
		return mDefinedTypes;
	}

	@Override
	public Set<String> getUndefinedTypes() {
		return mIncompleteType;
	}

	@Override
	public ASTType cType2AstType(final ILocation loc, final CType cType) {
		if (cType instanceof CPrimitive) {
			return cPrimitive2AstType(loc, (CPrimitive) cType);
		} else if (cType instanceof CPointer) {
			return constructPointerType(loc);
		} else if (cType instanceof CArray) {
			/*
			 * note: we are using nested Boogie array types (thus the Boogie ArrayType we use will always have a
			 *  one-element array for the index types
			 */
			final CArray cArrayType = (CArray) cType;
			final ASTType indexType = cType2AstType(loc, cArrayType.getBound().getCType());
			final String[] typeParams = new String[0];
			final ASTType valueType = cType2AstType(loc, cArrayType.getValueType());
			return new ArrayType(loc, typeParams, new ASTType[] { indexType }, valueType);

//			final CArray cart = (CArray) cType;
//			final ASTType[] indexTypes = new ASTType[cart.getDimensions().length];
//			final String[] typeParams = new String[0]; // new String[cart.getDimensions().length];
//
//			for (int i = 0; i < cart.getDimensions().length; i++) {
//				indexTypes[i] = cType2AstType(loc, cart.getDimensions()[i].getCType());
//			}
//			// return new ArrayType(loc, typeParams, indexTypes, cType2AstType(loc, cart.getValueType()));
//
//			ASTType arrayType = cType2AstType(loc, cart.getValueType());
//			for (int i = 0; i < cart.getDimensions().length; i++) {
//				arrayType = new ArrayType(loc, typeParams, new ASTType[] { indexTypes[i] }, arrayType);
//			}
//			return arrayType;
		} else if (cType instanceof CStruct) {
			final CStruct cstruct = (CStruct) cType;
			if (cstruct.isIncomplete()) {
				return null;
			}
			final VarList[] fields = new VarList[cstruct.getFieldCount()];
			for (int i = 0; i < cstruct.getFieldCount(); i++) {
				fields[i] = new VarList(loc, new String[] { cstruct.getFieldIds()[i] },
						cType2AstType(loc, cstruct.getFieldTypes()[i]));
			}
			return new StructType(loc, fields);
		} else if (cType instanceof CNamed) {
			// should work as we save the unique typename we computed in CNamed, not the name from the source c file
			return new NamedType(loc, ((CNamed) cType).getName(), new ASTType[0]);
		} else if (cType instanceof CFunction) {
			// throw new UnsupportedSyntaxException(loc, "how to translate function type?");
			// return null;
			return constructPointerType(loc);
		} else if (cType instanceof CEnum) {
			// return new NamedType(loc, ((CEnum) cType).getIdentifier(), new ASTType[0]);
			return cPrimitive2AstType(loc, new CPrimitive(CPrimitives.INT));
		}
		throw new UnsupportedSyntaxException(loc, "unknown type");
	}

	private ASTType cPrimitive2AstType(final ILocation loc, final CPrimitive cPrimitive) {
		switch (cPrimitive.getGeneralType()) {
		case VOID:
			return null; // (alex:) seems to be lindemm's convention, see FunctionHandler.isInParamVoid(..)
		case INTTYPE:
			if (mBitvectorTranslation) {
				return new NamedType(loc, "C_" + cPrimitive.getType().toString(), new ASTType[0]);
			}
			return new PrimitiveType(loc, SFO.INT);
		case FLOATTYPE:
			mFloatingTypesNeeded = true;
			if (mBitvectorTranslation) {
				return new NamedType(loc, "C_" + cPrimitive.getType().toString(), new ASTType[0]);
			}
			return new PrimitiveType(loc, SFO.REAL);
		default:
			throw new UnsupportedSyntaxException(loc, "unknown primitive type");
		}
	}

	public ASTType bytesize2asttype(final ILocation loc, final CPrimitiveCategory generalprimitive,
			final int bytesize) {
		switch (generalprimitive) {
		case VOID:
			throw new UnsupportedOperationException();
		case INTTYPE:
			if (mBitvectorTranslation) {
				final int bitsize = bytesize * 8;
				final String name = "bv" + bitsize;
				final ASTType astType = new PrimitiveType(loc, name);
				return astType;
			}
			return new PrimitiveType(loc, SFO.INT);
		case FLOATTYPE:
			mFloatingTypesNeeded = true;
			if (mBitvectorTranslation) {
				final int bitsize = bytesize * 8;
				final String name = "bv" + bitsize;
				final ASTType astType = new PrimitiveType(loc, name);
				return astType;
			}
			return new PrimitiveType(loc, SFO.REAL);
		default:
			throw new UnsupportedSyntaxException(loc, "unknown primitive type");
		}
	}

	@Override
	public void beginScope() {
		mDefinedTypes.beginScope();
	}

	@Override
	public void endScope() {
		assert !mDefinedTypes.isEmptyScope();
		mDefinedTypes.endScope();
	}

	@Override
	public void addDefinedType(final String id, final TypesResult type) {
		mDefinedTypes.put(id, type);
	}

	@Override
	public ASTType constructPointerType(final ILocation loc) {
		mPointerTypeNeeded = true;
		return new NamedType(null, SFO.POINTER, new ASTType[0]);
	}

	@Override
	public BoogieType constructBoogiePointerType() {
		return mBoogiePointerType;
	}

	@Override
	public BoogieType astTypeToBoogieType(final ASTType astType) {
		// TODO
		throw new AssertionError("TODO");
	}

	/**
	 * Construct list of type declarations that are needed because the corresponding types are introduced by the
	 * translation, e.g., pointers.
	 */
	public ArrayList<Declaration> constructTranslationDefiniedDelarations(final ILocation tuLoc,
			final ExpressionTranslation expressionTranslation) {
		final ArrayList<Declaration> decl = new ArrayList<>();
		if (mPointerTypeNeeded) {
			final VarList fBase = new VarList(tuLoc, new String[] { SFO.POINTER_BASE },
					cType2AstType(tuLoc, expressionTranslation.getCTypeOfPointerComponents()));
			final VarList fOffset = new VarList(tuLoc, new String[] { SFO.POINTER_OFFSET },
					cType2AstType(tuLoc, expressionTranslation.getCTypeOfPointerComponents()));
			final VarList[] fields = new VarList[] { fBase, fOffset };
			final ASTType pointerType = new StructType(tuLoc, fields);
			// Pointer is non-finite, right? (ZxZ)..
			decl.add(new TypeDeclaration(tuLoc, new Attribute[0], false, SFO.POINTER, new String[0], pointerType));
		}
		return decl;
	}

	public boolean areFloatingTypesNeeded() {
		return mFloatingTypesNeeded;
	}

	public static boolean isAggregateCType(final CType cTypeRaw) {
		final CType cType = cTypeRaw.getUnderlyingType();

		if (cType instanceof CPrimitive || cType instanceof CEnum || cType instanceof CPointer
				|| cType instanceof CUnion || cType instanceof CFunction) {
			return false;
		} else if (cType instanceof CArray || cType instanceof CStruct) {
			return true;
		} else {
			throw new UnsupportedOperationException("missed a type??");
		}
	}

	/**
	 * Checks if two CTypes are equivalent. Replaces (some of) our uses of CType.equals(..).
	 *
	 * Avoids the potential endless recursion of the implementation of CType.equals(..) (which we should replace some
	 * time (Nov 17).
	 *
	 * Applications: (unclear, collect here)
	 *
	 * @param type1
	 * @param type2
	 * @return
	 */
	public static boolean areMatchingTypes(final CType type1, final CType type2) {
		return areMatchingTypes(type1, type2, new SymmetricHashRelation<>());
	}

	private static boolean areMatchingTypes(final CType type1, final CType type2,
			final SymmetricHashRelation<CType> visitedPairs) {

		final CType ulType1 = type1.getUnderlyingType();
		final CType ulType2 = type2.getUnderlyingType();

		if (!ulType1.getClass().equals(ulType2.getClass())) {
			return false;
		}

		if (ulType1.getClass().equals(CPrimitive.class)) {
			return areMatchingTypes((CPrimitive) ulType1, (CPrimitive) ulType2, visitedPairs);
		} else if (ulType1.getClass().equals(CEnum.class)) {
			return areMatchingTypes((CEnum) ulType1, (CEnum) ulType2, visitedPairs);
		} else if (ulType1.getClass().equals(CPointer.class)) {
			return areMatchingTypes((CPointer) ulType1, (CPointer) ulType2, visitedPairs);
		} else if (ulType1.getClass().equals(CUnion.class)) {
			return areMatchingTypes((CUnion) ulType1, (CUnion) ulType2, visitedPairs);
		} else if (ulType1.getClass().equals(CStruct.class)) {
			return areMatchingTypes((CStruct) ulType1, (CStruct) ulType2, visitedPairs);
		} else if (ulType1.getClass().equals(CArray.class)) {
			return areMatchingTypes((CArray) ulType1, (CArray) ulType2, visitedPairs);
		} else if (ulType1.getClass().equals(CFunction.class)) {
			return areMatchingTypes((CFunction) ulType1, (CFunction) ulType2, visitedPairs);
		} else {
			throw new UnsupportedOperationException("unknown CType");
		}
	}

	private static boolean areMatchingTypes(final CPrimitive type1, final CPrimitive type2,
			final SymmetricHashRelation<CType> visitedPairs) {
		return type1.getType() == type2.getType();
	}

	private static boolean areMatchingTypes(final CEnum type1, final CEnum type2,
			final SymmetricHashRelation<CType> visitedPairs) {

		if (!(type1.getIdentifier().equals(type2.getIdentifier()))) {
			return false;
		}
		if (type1.getFieldIds().length != type2.getFieldIds().length) {
			return false;
		}
		for (int i = 0; i < type1.getFieldIds().length; i++) {
			if (!(type1.getFieldIds()[i].equals(type2.getFieldIds()[i]))) {
				return false;
			}
		}
		return true;
	}

	private static boolean areMatchingTypes(final CPointer type1, final CPointer type2,
			final SymmetricHashRelation<CType> visitedPairs) {
		return areMatchingTypes(type1.getTargetType(), type2.getTargetType(), visitedPairs);
	}

	private static boolean areMatchingTypes(final CFunction type1, final CFunction type2,
			final SymmetricHashRelation<CType> visitedPairs) {
		if (visitedPairs.containsPair(type1, type2)) {
			// found a cycle in the c type --> types match
			return true;
		}
		final SymmetricHashRelation<CType> visitedPairsNew = new SymmetricHashRelation<>(visitedPairs);
		visitedPairsNew.addPair(type1, type2);

		if (type1.getParameterTypes().length != type2.getParameterTypes().length) {
			return false;
		}
		if (!areMatchingTypes(type1.getResultType(), type2.getResultType(), visitedPairsNew)) {
			return false;
		}
		for (int i = 0; i < type1.getParameterTypes().length; i++) {
			if (!areMatchingTypes(type1.getParameterTypes()[i].getType(), type2.getParameterTypes()[i].getType())) {
				return false;
			}
		}
		if (type1.takesVarArgs() != type2.takesVarArgs()) {
			return false;
		}
		return true;
	}

	private static boolean areMatchingTypes(final CStruct type1, final CStruct type2,
			final SymmetricHashRelation<CType> visitedPairs) {
		if (visitedPairs.containsPair(type1, type2)) {
			// found a cycle in the c type --> types match
			return true;
		}
		final SymmetricHashRelation<CType> visitedPairsNew = new SymmetricHashRelation<>(visitedPairs);
		visitedPairsNew.addPair(type1, type2);

		if (type1.getFieldIds().length != type2.getFieldIds().length) {
			return false;
		}
		for (int i = 0; i < type1.getFieldIds().length - 1; i++) {
			if (!(type1.getFieldIds()[i].equals(type2.getFieldIds()[i]))) {
				return false;
			}
		}
		if (type1.getFieldTypes().length != type2.getFieldTypes().length) {
			return false;
		}
		for (int i = 0; i < type1.getFieldTypes().length; i++) {
			if (!areMatchingTypes(type1.getFieldTypes()[i], type2.getFieldTypes()[i], visitedPairsNew)) {
				return false;
			}
		}
		return true;
	}

	private static boolean areMatchingTypes(final CArray type1, final CArray type2,
			final SymmetricHashRelation<CType> visitedPairs) {
		if (!areMatchingTypes(type1.getValueType(), type2.getValueType(), visitedPairs)) {
			return false;
		}
		if (!type1.getBound().toString().equals(type2.getBound().toString())) {
			return false;
		}

		return true;
	}

	/**
	 * Checks if type1 and type2 have "compatible structure or union type", as in C11 6.7.9.13 The initializer for a
	 * structure or union object that has automatic storage duration shall be either an initializer list as described
	 * below, or a single expression that has compatible structure or union type.
	 *
	 * @param type1
	 * @param type2
	 * @return
	 */
	public static boolean isCompatibleType(final CType type1, final CType type2) {
		// TODO: check the notion of compatibility with the standard
		if (isCharArray(type1) && isCharArray(type2)) {
			return true;
		}
		if (type1 instanceof CStruct && type2 instanceof CStruct) {
			return areMatchingTypes(type1, type2);
		}
		return false;
	}

	public static boolean isCharArray(final CType cTypeRaw) {
		final CType cType = cTypeRaw.getUnderlyingType();
		if (!(cType instanceof CArray)) {
			return false;
		}
		final CArray cArrayType = (CArray) cType;
		if (!(cArrayType.getValueType().getUnderlyingType() instanceof CPrimitive)) {
			return false;
		}
		final CPrimitive primitiveValueType = (CPrimitive) cArrayType.getValueType().getUnderlyingType();
		if (primitiveValueType.getType() != CPrimitives.CHAR && primitiveValueType.getType() != CPrimitives.UCHAR
				&& primitiveValueType.getType() != CPrimitives.SCHAR) {
			return false;
		}
		return true;
	}

	@Override
	public ICHandler getCHandler() {
		assert mCHandler != null : "plan is to call setCHandler in the CHandler constructor (the CHandler constructor "
				+ "takes a typeHandler as argument)";
		return mCHandler;
	}

	@Override
	public void setCHandler(final CHandler cHandler) {
		assert cHandler != null;
		assert mCHandler == null : "don't call this twice";
		mCHandler = cHandler;
	}
}
