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

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.IASTCompositeTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTElaboratedTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTEnumerationSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTEnumerationSpecifier.IASTEnumerator;
import org.eclipse.cdt.core.dom.ast.IASTNamedTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclSpecifier;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieStructType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.IMemoryPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryPointerFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.StaticObjectsHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CNamed;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitiveCategory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStructOrUnion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStructOrUnion.StructOrUnion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.ICType;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.LinkedScopedHashMap;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
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

	private final Map<String, CStructOrUnion> mIncompleteCStructOrUnionObjects = new HashMap<>();
	private final HashRelation<String, CEnum> mIncompleteCEnumObjects = new HashRelation<>();

	/**
	 * States if an ASTNode for the pointer type was constructed and hence this type has to be declared.
	 */
	private boolean mPointerTypeNeeded = false;

	/**
	 * Is true iff we yet processed a floating type. (And hence floating types have to be added to Boogie).
	 */
	private boolean mFloatingTypesNeeded = false;

	private final INameHandler mNameHandler;

	private final TypeSizes mTypeSizes;

	private final FlatSymbolTable mSymboltable;

	private final TranslationSettings mTranslationSettings;
	private final LocationFactory mLocationFactory;
	private final StaticObjectsHandler mStaticObjectsHandler;

	private final IMemoryPointer mMemoryPointer;

	/**
	 * If there is an incomplete type X that has not yet been completed and occurs in a statement of the form
	 * <code>typedef X Y</code>, then the pair (X,Y) is in this relation.
	 */
	private final HashRelation<String, String> mNamedIncompleteTypes = new HashRelation<>();
	private final Map<String, ICType> mLibraryTypes = new HashMap<>();

	public TypeHandler(final INameHandler nameHandler, final TypeSizes typeSizes, final FlatSymbolTable symboltable,
			final TranslationSettings translationSettings, final LocationFactory locationFactory,
			final StaticObjectsHandler staticObjectsHandler) {
		mNameHandler = nameHandler;
		mTypeSizes = typeSizes;
		mDefinedTypes = new LinkedScopedHashMap<>();
		mIncompleteType = new LinkedHashSet<>();
		mSymboltable = symboltable;
		mTranslationSettings = translationSettings;
		mLocationFactory = locationFactory;
		mStaticObjectsHandler = staticObjectsHandler;
		mMemoryPointer = MemoryPointerFactory.createMemoryPointer(mTranslationSettings,
				(BoogieType) cType2AstType(null, translationSettings.getCTypeOfPointerComponents()).getBoogieType(),
				typeSizes);
	}

	public TypeHandler(final INameHandler nameHandler, final TypeSizes typeSizes, final FlatSymbolTable symboltable,
			final TranslationSettings translationSettings, final LocationFactory locationFactory,
			final StaticObjectsHandler staticObjectsHandler, final TypeHandler prerunTypeHandler) {
		mNameHandler = nameHandler;
		mTypeSizes = typeSizes;
		mSymboltable = symboltable;
		mTranslationSettings = translationSettings;
		mLocationFactory = locationFactory;
		mStaticObjectsHandler = staticObjectsHandler;

		// reuse typehandler parts from prerun
		mMemoryPointer = prerunTypeHandler.mMemoryPointer;
		mDefinedTypes = prerunTypeHandler.mDefinedTypes;
		mIncompleteType = prerunTypeHandler.mIncompleteType;
	}

	@Override
	public void requestFloatingTypes() {
		mFloatingTypesNeeded = true;
	}

	@Override
	public Result visit(final IDispatcher main, final IASTSimpleDeclSpecifier node) {
		// we have model.boogie.ast.PrimitiveType, which should
		// only contain BOOL, INT, REAL ...
		final ILocation loc = mLocationFactory.createCLocation(node);
		switch (node.getType()) {
		case IASTSimpleDeclSpecifier.t_void: {
			// there is no void in Boogie,
			// so we simply have no result variable.
			final CPrimitive cvar = new CPrimitive(node);
			return new TypesResult(null, false, true, cvar);
		}
		case IASTSimpleDeclSpecifier.t_unspecified:
		case IASTSimpleDeclSpecifier.t_bool:
		case IASTSimpleDeclSpecifier.t_char:
		case IASTSimpleDeclSpecifier.t_int:
		case IASTSimpleDeclSpecifier.t_int128: {
			// so int is also a primitive type
			// NOTE: in a extended implementation we should
			// handle here different types of int (short, long,...)
			final CPrimitive cvar = new CPrimitive(node);
			return new TypesResult(cPrimitive2AstType(loc, cvar), node.isConst(), false, cvar);
		}
		case IASTSimpleDeclSpecifier.t_double:
		case IASTSimpleDeclSpecifier.t_float:
		case IASTSimpleDeclSpecifier.t_float128: {
			// floating point number are not supported by Ultimate,
			// somehow we treat it here as REALs
			final CPrimitive cvar = new CPrimitive(node);
			return new TypesResult(new PrimitiveType(loc, BoogieType.TYPE_REAL, SFO.REAL), node.isConst(), false, cvar);
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
				final ICType cType = ((ExpressionResult) opRes).getLrValue().getCType();
				return new TypesResult(cType2AstType(loc, cType), node.isConst(), false, cType);
			} else if (opRes instanceof DeclaratorResult) {
				final var declResult = (DeclaratorResult) opRes;
				if (!declResult.hasNoSideEffects()) {
					throw new AssertionError("passing side-effects from DeclaratorResults is not yet implemented");
				}
				final ICType cType = declResult.getDeclaration().getType();
				return new TypesResult(cType2AstType(loc, cType), node.isConst(), false, cType);
			}
		}
		default:
			// long, long long, and short are the same as int, iff there are
			// no restrictions / asserts in boogie
			if (node.isLongLong() || node.isLong() || node.isShort() || node.isUnsigned()) {
				final CPrimitive cvar = new CPrimitive(node);
				return new TypesResult(new PrimitiveType(loc, BoogieType.TYPE_INT, SFO.INT), node.isConst(), false,
						cvar);
			}
			// if we do not find a type we cancel with Exception
			final String msg = "TypeHandler: We do not support this type: " + node.getType() + "!";
			throw new UnsupportedSyntaxException(loc, msg);
		}
	}

	@Override
	public Result visit(final IDispatcher main, final IASTNamedTypeSpecifier node) {
		final ILocation loc = mLocationFactory.createCLocation(node);
		final String cId = node.getName().toString();
		final String modifiedName = mSymboltable.applyMultiparseRenaming(node.getContainingFilename(), cId);
		final SymbolTableValue stv = mSymboltable.findCSymbol(node, modifiedName);
		if (stv == null) {
			final ICType libraryType = mLibraryTypes.get(cId);
			if (libraryType != null) {
				return new TypesResult(cType2AstType(loc, libraryType), node.isConst(), libraryType.isVoidType(),
						libraryType);
			}
			final String msg = "Undefined type " + cId;
			throw new UnsupportedSyntaxException(loc, msg);
		}
		final ICType cType = stv.getCType();
		final BoogieType boogieType = getBoogieTypeForCType(cType);
		final String bId = stv.getBoogieName();
		// TODO: replace constants "false, false"
		final boolean isConstant = false;
		final boolean isVoid = false;
		return new TypesResult(new NamedType(loc, boogieType, bId, new ASTType[0]), isConstant, isVoid,
				new CNamed(bId, cType));
	}

	@Override
	public Result visit(final IDispatcher main, final IASTEnumerationSpecifier node) {
		final ILocation loc = mLocationFactory.createCLocation(node);
		final String cId = node.getName().toString();
		final String rslvName = mSymboltable.applyMultiparseRenaming(node.getContainingFilename(), cId);
		// values of enum have type int
		final CPrimitive intType = new CPrimitive(CPrimitives.INT);
		final String enumId = mNameHandler.getUniqueIdentifier(node, node.getName().toString(),
				mSymboltable.getCScopeId(node), false, intType, DeclarationInformation.DECLARATIONINFO_GLOBAL);
		final int nrFields = node.getEnumerators().length;
		final String[] fNames = new String[nrFields];
		Expression valueOfPrecedingEnumConstant = null;

		final List<Pair<ConstDeclaration, Axiom>> constDecls = new ArrayList<>();

		for (int i = 0; i < nrFields; i++) {
			final IASTEnumerator e = node.getEnumerators()[i];
			fNames[i] = e.getName().toString();
			final Expression specifiedValue;
			if (e.getValue() != null) {
				final ExpressionResult rex = (ExpressionResult) main.dispatch(e.getValue());
				// TODO Frank 2022-11-22: rex might contain statements (e.g. overflow-assertions), but they are ignored
				// here! We should probably crash instead. But we could try to remove trivial assertions additionally.
				specifiedValue = rex.getLrValue().getValue();
			} else {
				specifiedValue = null;
			}
			final Expression value = constructEnumValue(loc, specifiedValue, valueOfPrecedingEnumConstant);
			final Pair<ConstDeclaration, Axiom> cd = handleEnumerationConstant(loc, enumId, fNames[i], value, node);
			constDecls.add(cd);
			valueOfPrecedingEnumConstant = value;
		}
		final CEnum cEnum = new CEnum(enumId, fNames);
		final ASTType at = cPrimitive2AstType(loc, intType);
		final TypesResult result = new TypesResult(at, false, false, cEnum);
		for (int i = 0; i < nrFields; i++) {
			final String fId = fNames[i];
			final Pair<ConstDeclaration, Axiom> cd = constDecls.get(i);
			mStaticObjectsHandler.addGlobalConstDeclaration(cd.getFirst(), new CDeclaration(cEnum, fId),
					cd.getSecond());
		}

		final String incompleteTypeName = "ENUM~" + rslvName;
		if (mIncompleteType.contains(incompleteTypeName)) {
			mIncompleteType.remove(incompleteTypeName);
			final TypesResult typeResult = mDefinedTypes.get(rslvName);
			final CEnum incompleteEnum = (CEnum) typeResult.getCType();
			// search for any typedefs that were made for the incomplete type
			// typedefs are made globally, so the CHandler has to do this
			mStaticObjectsHandler.completeTypeDeclaration(cEnum.getName(), cEnum, this);
			final CEnum completeEnum = incompleteEnum.complete(cEnum);
			mDefinedTypes.put(rslvName, TypesResult.create(typeResult, completeEnum));
		}

		if (!enumId.equals(SFO.EMPTY)) {
			mDefinedTypes.put(rslvName, result);
		}

		return result;
	}

	@Override
	public Result visit(final IDispatcher main, final IASTElaboratedTypeSpecifier node) {
		final ILocation loc = mLocationFactory.createCLocation(node);
		if (node.getKind() == IASTElaboratedTypeSpecifier.k_struct
				|| node.getKind() == IASTElaboratedTypeSpecifier.k_enum
				|| node.getKind() == IASTElaboratedTypeSpecifier.k_union) {
			final String type = node.getName().toString();
			final String rslvName = mSymboltable.applyMultiparseRenaming(node.getContainingFilename(), type);

			final TypesResult originalType = mDefinedTypes.get(rslvName);
			if (originalType != null) {
				// --> we have a normal struct, union or enum declaration
				return new TypesResult(originalType.getAstType(), originalType.isConst(), originalType.isVoid(),
						originalType.getCType());
			}
			// --> This is a definition of an incomplete struct, enum or union.
			String incompleteTypeName;
			if (node.getKind() == IASTElaboratedTypeSpecifier.k_struct) {
				incompleteTypeName = "STRUCT~" + rslvName;
			} else if (node.getKind() == IASTElaboratedTypeSpecifier.k_union) {
				incompleteTypeName = "UNION~" + rslvName;
			} else {
				incompleteTypeName = "ENUM~" + rslvName;
			}

			mIncompleteType.add(incompleteTypeName);
			// FIXME : not sure, if null is a good idea!
			ICType ctype;
			if (node.getKind() == IASTElaboratedTypeSpecifier.k_struct) {
				ctype = new CStructOrUnion(StructOrUnion.STRUCT, type);
				addIncompleteStructOrUnion(rslvName, (CStructOrUnion) ctype);
			} else if (node.getKind() == IASTElaboratedTypeSpecifier.k_union) {
				ctype = new CStructOrUnion(StructOrUnion.UNION, type);
				addIncompleteStructOrUnion(rslvName, (CStructOrUnion) ctype);
			} else {
				ctype = new CEnum(type);
				mIncompleteCEnumObjects.addPair(rslvName, (CEnum) ctype);
			}
			final TypesResult r = new TypesResult(
					new NamedType(loc, BoogieType.TYPE_ERROR, incompleteTypeName, new ASTType[0]), false, false, ctype);

			mDefinedTypes.put(rslvName, r);

			return r;
		}
		final String msg = "Not yet implemented: Spec [" + node.getKind() + "] of " + node.getClass();
		throw new UnsupportedSyntaxException(loc, msg);
	}

	private void addIncompleteStructOrUnion(final String name, final CStructOrUnion structOrUnion) {
		final var existing = mIncompleteCStructOrUnionObjects.get(name);
		if (existing != null && !existing.equals(structOrUnion)) {
			throw new AssertionError("too many types");
		}
		mIncompleteCStructOrUnionObjects.put(name, structOrUnion);
	}

	@Override
	public Result visit(final IDispatcher main, final IASTCompositeTypeSpecifier node) {
		final ILocation loc = mLocationFactory.createCLocation(node);
		// TODO : include inactives? what are inactives?
		final ArrayList<String> fNames = new ArrayList<>();
		final ArrayList<ICType> fTypes = new ArrayList<>();
		final ArrayList<Integer> bitFieldWidths = new ArrayList<>();
		for (final IASTDeclaration dec : node.getDeclarations(false)) {
			final Result r = main.dispatch(dec);
			if (r instanceof DeclarationResult) {
				final DeclarationResult rdec = (DeclarationResult) r;
				for (final CDeclaration declaration : rdec.getDeclarations()) {
					fNames.add(declaration.getName());
					fTypes.add(declaration.getType());
					bitFieldWidths.add(declaration.getBitfieldSize());
				}
			} else if (r instanceof SkipResult) { // skip ;)
			} else {
				final String msg = "Unexpected syntax in struct declaration!";
				throw new UnsupportedSyntaxException(loc, msg);
			}
		}

		final String cId = node.getName().toString();
		final String rslvName = mSymboltable.applyMultiparseRenaming(node.getContainingFilename(), cId);
		final StructOrUnion isStructOrUnion;
		if (node.getKey() == IASTCompositeTypeSpecifier.k_struct) {
			isStructOrUnion = StructOrUnion.STRUCT;
		} else if (node.getKey() == IASTCompositeTypeSpecifier.k_union) {
			isStructOrUnion = StructOrUnion.UNION;
		} else {
			throw new UnsupportedOperationException();
		}

		final String identifier = CStructOrUnion.getPrefix(isStructOrUnion) + rslvName;

		if (mIncompleteCStructOrUnionObjects.containsKey(rslvName)) {
			final CStructOrUnion structOrUnion = mIncompleteCStructOrUnionObjects.get(rslvName);
			structOrUnion.complete(fNames, fTypes, bitFieldWidths);
			mStaticObjectsHandler.completeTypeDeclaration(structOrUnion.getName(), structOrUnion, this);
			final TypesResult typeResult = mDefinedTypes.get(rslvName);
			mDefinedTypes.put(rslvName, TypesResult.create(typeResult, structOrUnion));
			if (mNamedIncompleteTypes.getDomain().contains(structOrUnion.getName())) {
				redirectNamedType(mNamedIncompleteTypes.getImage(structOrUnion.getName()), structOrUnion,
						node.getParent());
			}

			mIncompleteCStructOrUnionObjects.remove(rslvName);
		}

		final CStructOrUnion cvar = new CStructOrUnion(isStructOrUnion, rslvName, fNames, fTypes, bitFieldWidths);

		// TODO : boogie type
		final NamedType namedType = new NamedType(loc, BoogieType.TYPE_ERROR, identifier, new ASTType[0]);
		final ASTType type = namedType;
		final TypesResult result = new TypesResult(type, false, false, cvar);

		if (mIncompleteType.remove(identifier)) {
			// final TypesResult typeResult = mDefinedTypes.get(rslvName);
			// final CStructOrUnion incompleteStruct = (CStructOrUnion) typeResult.getCType();
			// search for any typedefs that were made for the incomplete type
			// typedefs are made globally, so the CHandler has to do this
			// mStaticObjectsHandler.completeTypeDeclaration(incompleteStruct, cvar, this);

			// final CStructOrUnion completeStruct = incompleteStruct.complete(cvar);
			// mDefinedTypes.put(rslvName, TypesResult.create(typeResult, completeStruct));
			// if (mNamedIncompleteTypes.getDomain().contains(incompleteStruct)) {
			// redirectNamedType(mNamedIncompleteTypes.getImage(incompleteStruct), completeStruct, node.getParent());
			// }
		}

		if (!cId.equals(SFO.EMPTY)) {
			mDefinedTypes.put(rslvName, result);
		}
		return result;
	}

	private void redirectNamedType(final Set<String> names, final CStructOrUnion completeStruct, final IASTNode hook) {
		final Map<String, ICType> alreadyRedirected = new HashMap<>();
		for (final String name : names) {
			constructUpdatedCNamedAndAddToSymbolTable(name, completeStruct, alreadyRedirected, hook);
		}
	}

	private ICType constructUpdatedCNamedAndAddToSymbolTable(final String name, final CStructOrUnion completeStruct,
			final Map<String, ICType> alreadyRedirected, final IASTNode hook) {
		if (alreadyRedirected.containsKey(name)) {
			return alreadyRedirected.get(name);
		}
		final SymbolTableValue oldStv = mSymboltable.findCSymbol(hook, name);
		if (oldStv == null) {
			throw new AssertionError("Unable to locate " + name + " in the symbol table");
		}

		ICType newDefiningType;
		if (oldStv.getCType() instanceof CNamed) {
			// end of chain not yet reached
			final var boogieId = ((CNamed) oldStv.getCType()).getName();
			final var cId = mSymboltable.getCIdForBoogieId(boogieId);

			final ICType definingTypeOfDefiningType =
					constructUpdatedCNamedAndAddToSymbolTable(cId, completeStruct, alreadyRedirected, hook);
			newDefiningType = new CNamed(name, definingTypeOfDefiningType);
		} else {
			newDefiningType = completeStruct;
		}

		final CDeclaration oldCDecl = oldStv.getCDecl();
		final CDeclaration newCDecl = new CDeclaration(newDefiningType, oldCDecl.getName(),
				oldCDecl.getIASTInitializer(), oldCDecl.getInitializer(), oldCDecl.isOnHeap(),
				oldCDecl.getStorageClass(), oldCDecl.getBitfieldSize());
		final SymbolTableValue val =
				new SymbolTableValue(oldStv.getBoogieName(), oldStv.getBoogieDecl(), oldStv.getAstType(), newCDecl,
						oldStv.getDeclarationInformation(), oldStv.getDeclarationNode(), oldStv.isIntFromPointer());
		mSymboltable.storeCSymbol(hook, name, val);
		alreadyRedirected.put(name, newDefiningType);
		return newDefiningType;
	}

	@Override
	public ASTType getTypeOfStructLHS(final FlatSymbolTable sT, final ILocation loc, final StructLHS lhs,
			final IASTNode hook) {
		final String[] flat = BoogieASTUtil.getLHSList(lhs);
		final String leftMostId = flat[0];
		assert leftMostId.equals(BoogieASTUtil.getLHSId(lhs));
		assert sT.containsBoogieSymbol(leftMostId);
		final String cId = sT.getCIdForBoogieId(leftMostId);
		assert sT.containsCSymbol(hook, cId);
		final ASTType t = cType2AstType(loc, sT.findCSymbol(hook, cId).getCType());
		return traverseForType(loc, t, flat, 1);
	}

	@Override
	public Set<String> getUndefinedTypes() {
		return Collections.unmodifiableSet(mIncompleteType);
	}

	@Override
	public ASTType cType2AstType(final ILocation loc, final ICType cType) {
		if (cType instanceof final CPrimitive primitive) {
			return cPrimitive2AstType(loc, primitive);
		} else if (cType instanceof CPointer) {
			return constructPointerType(loc);
		} else if (cType instanceof final CArray cArrayType) {
			/*
			 * note: we are using nested Boogie array types (thus the Boogie ArrayType we use will always have a
			 * one-element array for the index types
			 */
			final ASTType indexType = cType2AstType(loc, cArrayType.getBound().getCType());
			final ASTType valueType = cType2AstType(loc, cArrayType.getValueType());
			final BoogieArrayType boogieType =
					BoogieType.createArrayType(0, new BoogieType[] { (BoogieType) indexType.getBoogieType() },
							(BoogieType) valueType.getBoogieType());
			return new ArrayType(loc, boogieType, new String[0], new ASTType[] { indexType }, valueType);
		} else if (cType instanceof final CStructOrUnion cstruct) {
			// if (cstruct.isIncomplete()) {
			// // TODO 2018-09-10: before I added this UnsupportedOperation
			// // Exception we just returned null which is probably a bad
			// // solution. Maybe callers should check for this case in advance.
			// // return null;
			// throw new UnsupportedOperationException("No Boogie because C type is incomplete: " + cType);
			// }
			final VarList[] fields = new VarList[cstruct.getFieldCount()];
			final String[] fieldNames = new String[cstruct.getFieldCount()];
			final BoogieType[] fieldBoogieTypes = new BoogieType[cstruct.getFieldCount()];
			for (int i = 0; i < cstruct.getFieldCount(); i++) {
				final ASTType fieldType = cType2AstType(loc, cstruct.getFieldTypes()[i]);
				fields[i] = new VarList(loc, new String[] { cstruct.getFieldIds()[i] }, fieldType);
				fieldNames[i] = cstruct.getFieldIds()[i];
				fieldBoogieTypes[i] = (BoogieType) fieldType.getBoogieType();
			}
			final BoogieStructType boogieType = BoogieType.createStructType(fieldNames, fieldBoogieTypes);
			return new StructType(loc, boogieType, fields);
		} else if (cType instanceof final CNamed cNamed) {
			final BoogieType boogieType;
			if (cType.getUnderlyingType().isIncomplete()) {
				boogieType = null;
			} else {
				boogieType = (BoogieType) cType2AstType(loc, cType.getUnderlyingType()).getBoogieType();
			}
			// should work as we save the unique typename we computed in CNamed, not the name from the source c file
			return new NamedType(loc, boogieType, cNamed.getName(), new ASTType[0]);
		} else if (cType instanceof CFunction) {
			return constructPointerType(loc);
		} else if (cType instanceof CEnum) {
			return cPrimitive2AstType(loc, new CPrimitive(CPrimitives.INT));
		}
		throw new UnsupportedSyntaxException(loc, "unknown type");
	}

	@Override
	public ASTType byteSize2AstType(final ILocation loc, final CPrimitiveCategory generalprimitive,
			final int bytesize) {
		return switch (generalprimitive) {
		case VOID:
			throw new UnsupportedOperationException();
		case INTTYPE:
			if (mTranslationSettings.isBitvectorTranslation()) {
				final int bitsize = bytesize * 8;
				final String name = "bv" + bitsize;
				yield new PrimitiveType(loc, BoogieType.createBitvectorType(bitsize), name);
			}
			yield new PrimitiveType(loc, BoogieType.TYPE_INT, SFO.INT);
		case FLOATTYPE:
			mFloatingTypesNeeded = true;
			if (mTranslationSettings.isBitvectorTranslation()) {
				final int bitsize = bytesize * 8;
				final String name = "bv" + bitsize;
				yield new PrimitiveType(loc, BoogieType.createBitvectorType(bitsize), name);
			}
			yield new PrimitiveType(loc, BoogieType.TYPE_REAL, SFO.REAL);
		};
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
		return new NamedType(loc, getBoogiePointerType(), SFO.POINTER, new ASTType[0]);
	}

	/**
	 * Construct list of type declarations that are needed because the corresponding types are introduced by the
	 * translation, e.g., pointers.
	 */
	public ArrayList<Declaration> constructTranslationDefinedDeclarations(final ILocation tuLoc) {
		final ArrayList<Declaration> decl = new ArrayList<>();
		if (mPointerTypeNeeded) {
			final var pointerDeclaration = mMemoryPointer.getTypeDeclaration(tuLoc);
			decl.add(pointerDeclaration);
		}
		return decl;
	}

	@Override
	public boolean areFloatingTypesNeeded() {
		return mFloatingTypesNeeded;
	}

	@Override
	public BoogieType getBoogieTypeForBoogieASTType(final ASTType asttype) {
		if (asttype == null) {
			return BoogieType.TYPE_ERROR;
		}
		final BoogieType result = (BoogieType) asttype.getBoogieType();
		assert result != null : asttype + " has no underlying Boogie type";
		return result;
	}

	@Override
	public BoogieType getBoogieTypeForSizeT() {
		return getBoogieTypeForCType(mTypeSizes.getSizeT());
	}

	@Override
	public BoogieType getBoogieTypeForCType(final ICType cTypeRaw) {
		final ICType cType = cTypeRaw.getUnderlyingType();

		if (cType instanceof final CPrimitive cPrimitive) {
			if (mTranslationSettings.isBitvectorTranslation()) {
				final Integer byteSize = mTypeSizes.getSize(cPrimitive.getType());
				return BoogieType.createBitvectorType(byteSize * 8);
			}
			return switch (cPrimitive.getGeneralType()) {
			case FLOATTYPE -> BoogieType.TYPE_REAL;
			case INTTYPE -> BoogieType.TYPE_INT;
			case VOID -> BoogieType.TYPE_ERROR;
			};
		} else if (cType instanceof CPointer) {
			return getBoogiePointerType();
		} else if (cType instanceof CEnum) {
			return getBoogieTypeForCType(new CPrimitive(CPrimitives.INT));
		} else if (cType instanceof final CArray cArrayType) {
			final BoogieType[] indexTypes =
					{ getBoogieTypeForCType(mTranslationSettings.getCTypeOfPointerComponents()) };
			final BoogieType valueType = getBoogieTypeForCType(cArrayType.getValueType());
			return BoogieType.createArrayType(0, indexTypes, valueType);
		} else if (cType instanceof CFunction) {
			return getBoogiePointerType();
		} else if (cType instanceof final CStructOrUnion cStructType) {
			final BoogieType[] boogieFieldTypes = new BoogieType[cStructType.getFieldCount()];
			for (int i = 0; i < cStructType.getFieldCount(); i++) {
				boogieFieldTypes[i] = getBoogieTypeForCType(cStructType.getFieldTypes()[i]);
			}
			return BoogieType.createStructType(cStructType.getFieldIds(), boogieFieldTypes);
		} else {
			throw new AssertionError("unknown type " + cType);
		}
	}

	@Override
	public BoogieType getBoogiePointerType() {
		return mMemoryPointer.getPointerType();
	}

	@Override
	public BoogieType getBoogieTypeForPointerComponents() {
		return getBoogieTypeForCType(mTranslationSettings.getCTypeOfPointerComponents());
	}

	/**
	 * @param enumConstId
	 *            Identifier of the enumeration constant as is appears in the C code.
	 */
	private Pair<ConstDeclaration, Axiom> handleEnumerationConstant(final ILocation loc, final String enumId,
			final String enumConstId, final Expression value, final IASTEnumerationSpecifier node) {
		final CPrimitive typeOfEnumIdentifiers = new CPrimitive(CPrimitive.CPrimitives.INT);
		// C standard says: "The identifiers in an enumerator list are declared
		// as constants that have type int ..."
		final ASTType enumAstType = cType2AstType(loc, typeOfEnumIdentifiers);
		final String boogieId = enumId + "~" + enumConstId;
		final VarList vl = new VarList(loc, new String[] { boogieId }, enumAstType);
		final ConstDeclaration cd = new ConstDeclaration(loc, new Attribute[0], false, vl, null, false);

		final Expression identifier =
				ExpressionFactory.constructIdentifierExpression(loc, getBoogieTypeForBoogieASTType(enumAstType),
						boogieId, new DeclarationInformation(StorageClass.GLOBAL, null));
		mSymboltable.storeCSymbol(node, enumConstId,
				new SymbolTableValue(boogieId, cd, enumAstType,
						new CDeclaration(typeOfEnumIdentifiers, enumConstId,
								CHandler.scConstant2StorageClass(node.getStorageClass())),
						DeclarationInformation.DECLARATIONINFO_GLOBAL, node, false, value));
		return new Pair<>(cd, new Axiom(loc, new Attribute[0],
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, identifier, value)));
	}

	/**
	 * Construct an {@link Expression} that represents the value of an enumeration constant according to C11 6.7.2.2.3.
	 * If the value of the enumeration constant is explicitly given in the C code, the argument for the parameter
	 * specifiedValue of this method is not null. Otherwise the argument is null and the value is determined by the
	 * value of the preceding enumeration constant in the list of this enumeration specifier.
	 */
	private Expression constructEnumValue(final ILocation loc, final Expression specifiedValue,
			final Expression valueOfPrecedingEnumConstant) {
		final CPrimitive typeOfEnumIdentifiers = new CPrimitive(CPrimitives.INT);
		if (specifiedValue != null) {
			// case where the value of the enumeration constant is explicitly defined by an integer constant expression
			if (specifiedValue instanceof IntegerLiteral) {
				return specifiedValue;
			}
			final BigInteger intValue;
			if (specifiedValue instanceof BooleanLiteral) {
				intValue = ((BooleanLiteral) specifiedValue).getValue() ? BigInteger.ONE : BigInteger.ZERO;
			} else {
				intValue = mTypeSizes.extractIntegerValue(specifiedValue, typeOfEnumIdentifiers);
			}
			if (intValue == null) {
				throw new AssertionError("not an integer constant: " + specifiedValue);
			}
			return mTypeSizes.constructLiteralForIntegerType(loc, typeOfEnumIdentifiers, intValue);
		}
		// case where the value of the enumeration constant is not explicitly defined by an integer constant expression
		// and hence the value of the preceding enumeration constant in the list defines the value of this enumeration
		// constant (see C11 6.7.2.2.3)
		if (valueOfPrecedingEnumConstant == null) {
			// case where this is the first enumeration constant in the list
			return mTypeSizes.constructLiteralForIntegerType(loc, typeOfEnumIdentifiers, BigInteger.ZERO);
		}
		final BigInteger intValue = mTypeSizes.extractIntegerValue(valueOfPrecedingEnumConstant, typeOfEnumIdentifiers);
		if (intValue == null) {
			throw new AssertionError("not an integer constant: " + valueOfPrecedingEnumConstant);
		}
		return mTypeSizes.constructLiteralForIntegerType(loc, typeOfEnumIdentifiers, intValue.add(BigInteger.ONE));
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
		if (t instanceof final ArrayType array) {
			return traverseForType(loc, array.getValueType(), flat, i);
		}
		if (t instanceof final StructType struct) {
			for (final VarList vl : struct.getFields()) {
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

	private ASTType cPrimitive2AstType(final ILocation loc, final CPrimitive cPrimitive) {
		final BoogieType boogieType = getBoogieTypeForCType(cPrimitive);

		return switch (cPrimitive.getGeneralType()) {
		case VOID:
			// (alex:) seems to be lindemm's convention, see FunctionHandler.isInParamVoid(..)
			yield null;
		case INTTYPE:
			if (mTranslationSettings.isBitvectorTranslation()) {
				yield new NamedType(loc, boogieType, "C_" + cPrimitive.getType().toString(), new ASTType[0]);
			}
			yield new PrimitiveType(loc, boogieType, SFO.INT);
		case FLOATTYPE:
			mFloatingTypesNeeded = true;
			if (mTranslationSettings.isBitvectorTranslation()) {
				yield new NamedType(loc, boogieType, "C_" + cPrimitive.getType().toString(), new ASTType[0]);
			}
			yield new PrimitiveType(loc, boogieType, SFO.REAL);
		};
	}

	@Override
	public void registerNamedIncompleteType(final String incompleteType, final String named) {
		mNamedIncompleteTypes.addPair(incompleteType, named);
	}

	@Override
	public CPrimitive getThreadIdType() {
		return new CPrimitive(CPrimitives.ULONG);
	}

	@Override
	public void addLibraryTypes(final Map<String, ICType> libraryTypes) {
		mLibraryTypes.putAll(libraryTypes);
	}

	public static boolean isCharArray(final ICType cTypeRaw) {
		return cTypeRaw.getUnderlyingType() instanceof final CArray cArrayType
				&& cArrayType.getValueType().getUnderlyingType() instanceof final CPrimitive cPrimitive
				&& (cPrimitive.getType() == CPrimitives.CHAR || cPrimitive.getType() == CPrimitives.UCHAR
						|| cPrimitive.getType() == CPrimitives.SCHAR);
	}

	@Override
	public IMemoryPointer memoryPointer() {
		return mMemoryPointer;
	}
}
