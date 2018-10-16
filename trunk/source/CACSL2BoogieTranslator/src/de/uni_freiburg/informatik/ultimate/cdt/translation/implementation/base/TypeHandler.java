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
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
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

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieStructType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.StaticObjectsHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.ICPossibleIncompleteType;
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
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.util.datastructures.LinkedScopedHashMap;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.SymmetricHashRelation;

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

	/**
	 * States if an ASTNode for the pointer type was constructed and hence this type has to be declared.
	 */
	private boolean mPointerTypeNeeded = false;

	/**
	 * Is true iff we yet processed a floating type. (And hence floating types have to be added to Boogie).
	 */
	private boolean mFloatingTypesNeeded = false;

	private final BoogieType mBoogiePointerType;

	private final CTranslationResultReporter mReporter;

	private final INameHandler mNameHandler;

	private final TypeSizes mTypeSizes;

	private final FlatSymbolTable mSymboltable;

	private final TranslationSettings mTranslationSettings;
	private final LocationFactory mLocationFactory;
	private final StaticObjectsHandler mStaticObjectsHandler;

	/**
	 * If there is an incomplete type X that has not yet been completed and occurs in a statement of the form typedef X
	 * Y, then the pair (X,Y) is in this relation.
	 */
	private final HashRelation<ICPossibleIncompleteType<?>, String> mNamedIncompleteTypes = new HashRelation<>();

	public TypeHandler(final CTranslationResultReporter reporter, final INameHandler nameHandler,
			final TypeSizes typeSizes, final FlatSymbolTable symboltable, final TranslationSettings translationSettings,
			final LocationFactory locationFactory, final StaticObjectsHandler staticObjectsHandler) {
		mReporter = reporter;
		mNameHandler = nameHandler;
		mTypeSizes = typeSizes;
		mDefinedTypes = new LinkedScopedHashMap<>();
		mIncompleteType = new LinkedHashSet<>();
		mSymboltable = symboltable;
		mTranslationSettings = translationSettings;
		mLocationFactory = locationFactory;
		mStaticObjectsHandler = staticObjectsHandler;

		// the type of pointer components currently (feb 18) is always int, but we are keeping all options..
		final BoogieType componentType =
				(BoogieType) cType2AstType(null, mTranslationSettings.getCTypeOfPointerComponents()).getBoogieType();
		mBoogiePointerType = BoogieType.createStructType(new String[] { SFO.POINTER_BASE, SFO.POINTER_OFFSET },
				new BoogieType[] { componentType, componentType });
	}

	public TypeHandler(final CTranslationResultReporter reporter, final INameHandler nameHandler,
			final TypeSizes typeSizes, final FlatSymbolTable symboltable, final TranslationSettings translationSettings,
			final LocationFactory locationFactory, final StaticObjectsHandler staticObjectsHandler,
			final TypeHandler prerunTypeHandler) {
		mReporter = reporter;
		mNameHandler = nameHandler;
		mTypeSizes = typeSizes;
		mSymboltable = symboltable;
		mTranslationSettings = translationSettings;
		mLocationFactory = locationFactory;
		mStaticObjectsHandler = staticObjectsHandler;

		// reuse typehandler parts from prerun
		mBoogiePointerType = prerunTypeHandler.mBoogiePointerType;
		mDefinedTypes = prerunTypeHandler.mDefinedTypes;
		mIncompleteType = prerunTypeHandler.mIncompleteType;
	}

	@Override
	public Result visit(final IDispatcher main, final IASTNode node) {
		final String msg = "TypeHandler: Not yet implemented: " + node.toString();
		final ILocation loc = mLocationFactory.createCLocation(node);
		throw new UnsupportedSyntaxException(loc, msg);
	}

	/**
	 * @deprecated is not supported in this handler! Do not use!
	 */
	@Deprecated
	@Override
	public Result visit(final IDispatcher main, final ACSLNode node) {
		throw new UnsupportedOperationException("Implementation Error: use ACSL handler for " + node.getClass());
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
			return (new TypesResult(null, false, true, cvar));
		}
		case IASTSimpleDeclSpecifier.t_unspecified: {
			final String msg = "unspecified type, defaulting to int";
			mReporter.warn(loc, msg);
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
				final CType cType = ((ExpressionResult) opRes).getLrValue().getCType();
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
				return (new TypesResult(new PrimitiveType(loc, BoogieType.TYPE_INT, SFO.INT), node.isConst(), false,
						cvar));
			}
			// if we do not find a type we cancel with Exception
			final String msg = "TypeHandler: We do not support this type!" + node.getType();
			throw new UnsupportedSyntaxException(loc, msg);
		}
	}

	@Override
	public Result visit(final IDispatcher main, final IASTNamedTypeSpecifier node) {
		final ILocation loc = mLocationFactory.createCLocation(node);
		if (node instanceof CASTTypedefNameSpecifier) {
			final String cId = node.getName().toString();

			// quick solution --> TODO: maybe make this dependent on includes,
			// maybe be more elegant (make an entry to symboltable, make a typedef in boogie file??)
			if (cId.equals("size_t") || cId.equals("ssize_t")) {
				return (new TypesResult(new PrimitiveType(loc, BoogieType.TYPE_REAL, SFO.REAL), node.isConst(), false,
						new CPrimitive(CPrimitives.UINT)));
			} else if (cId.equals("__builtin_va_list")) {
				return (new TypesResult(constructPointerType(loc), node.isConst(), false,
						new CPointer(new CPrimitive(CPrimitives.CHAR))));
			} else if (cId.equals("__pthread_list_t")) {
				return (new TypesResult(constructPointerType(loc), node.isConst(), false,
						new CPointer(new CPrimitive(CPrimitives.VOID))));
			} else {
				final String modifiedName = mSymboltable.applyMultiparseRenaming(node.getContainingFilename(), cId);
				final SymbolTableValue stv = mSymboltable.findCSymbol(node, modifiedName);
				if (stv == null) {
					final String msg = "Undefined type " + cId;
					throw new UnsupportedSyntaxException(loc, msg);
				}
				final CType cType = stv.getCType();
				final BoogieType boogieType = getBoogieTypeForCType(cType);
				final String bId = stv.getBoogieName();
				// TODO: replace constants "false, false"
				final boolean isConstant = false;
				final boolean isVoid = false;
				return new TypesResult(new NamedType(loc, boogieType, bId, new ASTType[0]), isConstant, isVoid,
						new CNamed(bId, cType));
			}
		}
		final String msg = "Unknown or unsupported type! " + node.getClass();
		throw new UnsupportedSyntaxException(loc, msg);
	}

	@Override
	public Result visit(final IDispatcher main, final IASTEnumerationSpecifier node) {
		final ILocation loc = mLocationFactory.createCLocation(node);
		final String cId = node.getName().toString();
		final String rslvName = mSymboltable.applyMultiparseRenaming(node.getContainingFilename(), cId);
		// values of enum have type int
		final CPrimitive intType = new CPrimitive(CPrimitives.INT);
		final String enumId = mNameHandler.getUniqueIdentifier(node, node.getName().toString(),
				mSymboltable.getCScopeId(node), false, intType);
		final int nrFields = node.getEnumerators().length;
		final String[] fNames = new String[nrFields];
		Expression valueOfPrecedingEnumConstant = null;

		final Expression[] fValues = new Expression[nrFields];
		final List<Pair<ConstDeclaration, Axiom>> constDecls = new ArrayList<>();

		for (int i = 0; i < nrFields; i++) {
			final IASTEnumerator e = node.getEnumerators()[i];
			fNames[i] = e.getName().toString();
			if (e.getValue() != null) {
				final ExpressionResult rex = (ExpressionResult) main.dispatch(e.getValue());
				fValues[i] = rex.getLrValue().getValue();
			} else {
				fValues[i] = null;
			}
			final Expression specifiedValue = fValues[i];
			final Expression value = constructEnumValue(loc, specifiedValue, valueOfPrecedingEnumConstant, node);
			final Pair<ConstDeclaration, Axiom> cd = handleEnumerationConstant(loc, enumId, fNames[i], value, node);
			constDecls.add(cd);
			valueOfPrecedingEnumConstant = value;
		}
		final CEnum cEnum = new CEnum(enumId, fNames, fValues);
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
			mStaticObjectsHandler.completeTypeDeclaration(incompleteEnum, cEnum, this);
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
				final TypesResult withoutBoogieTypedef = new TypesResult(originalType.getAstType(),
						originalType.isConst(), originalType.isVoid(), originalType.getCType());
				return withoutBoogieTypedef;
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
			CType ctype;
			if (node.getKind() == IASTElaboratedTypeSpecifier.k_struct) {
				ctype = new CStructOrUnion(StructOrUnion.STRUCT, type);
			} else if (node.getKind() == IASTElaboratedTypeSpecifier.k_union) {
				ctype = new CStructOrUnion(StructOrUnion.UNION, type);
			} else {
				ctype = new CEnum(type);
			}
			final TypesResult r = new TypesResult(
					new NamedType(loc, BoogieType.TYPE_ERROR, incompleteTypeName, new ASTType[0]), false, false, ctype);

			mDefinedTypes.put(rslvName, r);

			return r;
		}
		final String msg = "Not yet implemented: Spec [" + node.getKind() + "] of " + node.getClass();
		throw new UnsupportedSyntaxException(loc, msg);
	}

	@Override
	public Result visit(final IDispatcher main, final IASTCompositeTypeSpecifier node) {
		final ILocation loc = mLocationFactory.createCLocation(node);
		// TODO : include inactives? what are inactives?
		final ArrayList<String> fNames = new ArrayList<>();
		final ArrayList<CType> fTypes = new ArrayList<>();
		final ArrayList<Integer> bitFieldWidths = new ArrayList<>();
		for (final IASTDeclaration dec : node.getDeclarations(false)) {
			final Result r = main.dispatch(dec);
			if (r instanceof DeclarationResult) {
				final DeclarationResult rdec = (DeclarationResult) r;
				for (final CDeclaration declaration : rdec.getDeclarations()) {
					fNames.add(declaration.getName());
					fTypes.add(declaration.getType());
					if (mTranslationSettings.useBitpreciseBitfields()) {
						if (declaration.getBitfieldSize() != -1) {
							final String msg = "bitfield implementation not yet bitprecise (soundness first)";
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

		final String cId = node.getName().toString();
		final String rslvName = mSymboltable.applyMultiparseRenaming(node.getContainingFilename(), cId);

		final StructOrUnion structOrUnion;
		if (node.getKey() == IASTCompositeTypeSpecifier.k_struct) {
			structOrUnion = StructOrUnion.STRUCT;
		} else if (node.getKey() == IASTCompositeTypeSpecifier.k_union) {
			structOrUnion = StructOrUnion.UNION;
		} else {
			throw new UnsupportedOperationException();
		}

		final String identifier = CStructOrUnion.getPrefix(structOrUnion) + rslvName;
		final CStructOrUnion cvar = new CStructOrUnion(structOrUnion, rslvName, fNames.toArray(new String[fNames.size()]),
				fTypes.toArray(new CType[fTypes.size()]), bitFieldWidths);

		// TODO : boogie type
		final NamedType namedType = new NamedType(loc, BoogieType.TYPE_ERROR, identifier, new ASTType[0]);
		final ASTType type = namedType;
		final TypesResult result = new TypesResult(type, false, false, cvar);

		if (mIncompleteType.remove(identifier)) {
			final TypesResult typeResult = mDefinedTypes.get(rslvName);
			final CStructOrUnion incompleteStruct = (CStructOrUnion) typeResult.getCType();
			// search for any typedefs that were made for the incomplete type
			// typedefs are made globally, so the CHandler has to do this
			mStaticObjectsHandler.completeTypeDeclaration(incompleteStruct, cvar, this);

			final CStructOrUnion completeStruct = incompleteStruct.complete(cvar);
			mDefinedTypes.put(rslvName, TypesResult.create(typeResult, completeStruct));
			if (mNamedIncompleteTypes.getDomain().contains(incompleteStruct)) {
				redirectNamedType(mNamedIncompleteTypes.getImage(incompleteStruct), completeStruct, node.getParent());
			}
		}

		if (!cId.equals(SFO.EMPTY)) {
			mDefinedTypes.put(rslvName, result);
		}
		return result;
	}

	private void redirectNamedType(final Set<String> names, final CStructOrUnion completeStruct, final IASTNode hook) {
		final Set<String> alreadyRedirected = new HashSet<>();
		for (final String name : names) {
			constructUpdatedCNamedAndAddToSymbolTable(name, completeStruct, alreadyRedirected, hook);
		}
	}

	private CType constructUpdatedCNamedAndAddToSymbolTable(final String name, final CStructOrUnion completeStruct,
			final Set<String> alreadyRedirected, final IASTNode hook) {
		if (alreadyRedirected.contains(name)) {
			return null;
		}
		final SymbolTableValue oldStv = mSymboltable.findCSymbol(hook, name);

		CType newDefiningType;
		if ((oldStv.getCType() instanceof CNamed)) {
			// end of chain not yet reached
			final CType definingTypeOfDefiningType = constructUpdatedCNamedAndAddToSymbolTable(
					((CNamed) oldStv.getCType()).getName(), completeStruct, alreadyRedirected, hook);
			newDefiningType = new CNamed(name, definingTypeOfDefiningType);
		} else {
			newDefiningType = completeStruct;
		}

		final CDeclaration oldCDecl = oldStv.getCDecl();
		final CDeclaration newCDecl = new CDeclaration(newDefiningType, oldCDecl.getName(),
				oldCDecl.getIASTInitializer(), oldCDecl.getInitializer(), oldCDecl.isOnHeap(),
				oldCDecl.getStorageClass(), oldCDecl.getBitfieldSize());
		final SymbolTableValue val = new SymbolTableValue(oldStv.getBoogieName(), oldStv.getBoogieDecl(), newCDecl,
				oldStv.getDeclarationInformation(), oldStv.getDeclarationNode(), oldStv.isIntFromPointer());
		mSymboltable.storeCSymbol(hook, name, val);
		alreadyRedirected.add(name);
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
	public ASTType cType2AstType(final ILocation loc, final CType cType) {
		if (cType instanceof CPrimitive) {
			return cPrimitive2AstType(loc, (CPrimitive) cType);
		} else if (cType instanceof CPointer) {
			return constructPointerType(loc);
		} else if (cType instanceof CArray) {
			/*
			 * note: we are using nested Boogie array types (thus the Boogie ArrayType we use will always have a
			 * one-element array for the index types
			 */
			final CArray cArrayType = (CArray) cType;
			final ASTType indexType = cType2AstType(loc, cArrayType.getBound().getCType());
			final ASTType valueType = cType2AstType(loc, cArrayType.getValueType());
			final BoogieArrayType boogieType =
					BoogieType.createArrayType(0, new BoogieType[] { (BoogieType) indexType.getBoogieType() },
							(BoogieType) valueType.getBoogieType());
			return new ArrayType(loc, boogieType, new String[0], new ASTType[] { indexType }, valueType);
		} else if (cType instanceof CStructOrUnion) {
			final CStructOrUnion cstruct = (CStructOrUnion) cType;
			if (cstruct.isIncomplete()) {
				// TODO 2018-09-10: before I added this UnsupportedOperation
				// Exception we just returned null which is probably a bad
				// solution. Maybe callers should check for this case in advance.
				// return null;
				throw new UnsupportedOperationException("No Boogie because C type is incomplete: " + cType);
			}
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
		} else if (cType instanceof CNamed) {
			final BoogieType boogieType;
			if (cType.getUnderlyingType().isIncomplete()) {
				boogieType = null;
			} else {
				boogieType = (BoogieType) cType2AstType(loc, cType.getUnderlyingType()).getBoogieType();
			}
			// should work as we save the unique typename we computed in CNamed, not the name from the source c file
			return new NamedType(loc, boogieType, ((CNamed) cType).getName(), new ASTType[0]);
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
		switch (generalprimitive) {
		case VOID:
			throw new UnsupportedOperationException();
		case INTTYPE:
			if (mTranslationSettings.isBitvectorTranslation()) {
				final int bitsize = bytesize * 8;
				final String name = "bv" + bitsize;
				final ASTType astType = new PrimitiveType(loc, BoogieType.createBitvectorType(bitsize), name);
				return astType;
			}
			return new PrimitiveType(loc, BoogieType.TYPE_INT, SFO.INT);
		case FLOATTYPE:
			mFloatingTypesNeeded = true;
			if (mTranslationSettings.isBitvectorTranslation()) {
				final int bitsize = bytesize * 8;
				final String name = "bv" + bitsize;
				final ASTType astType = new PrimitiveType(loc, BoogieType.createBitvectorType(bitsize), name);
				return astType;
			}
			return new PrimitiveType(loc, BoogieType.TYPE_REAL, SFO.REAL);
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
		return new NamedType(loc, getBoogiePointerType(), SFO.POINTER, new ASTType[0]);
	}

	@Override
	public BoogieType astTypeToBoogieType(final ASTType astType) {
		if (astType == null) {
			// "null" astType represents a void type
			return BoogieType.TYPE_ERROR;
		}
		return (BoogieType) astType.getBoogieType();
	}

	/**
	 * Construct list of type declarations that are needed because the corresponding types are introduced by the
	 * translation, e.g., pointers.
	 */
	public ArrayList<Declaration> constructTranslationDefinedDeclarations(final ILocation tuLoc,
			final ExpressionTranslation expressionTranslation) {
		final ArrayList<Declaration> decl = new ArrayList<>();
		if (mPointerTypeNeeded) {
			final VarList fBase = new VarList(tuLoc, new String[] { SFO.POINTER_BASE },
					cType2AstType(tuLoc, expressionTranslation.getCTypeOfPointerComponents()));
			final VarList fOffset = new VarList(tuLoc, new String[] { SFO.POINTER_OFFSET },
					cType2AstType(tuLoc, expressionTranslation.getCTypeOfPointerComponents()));
			final VarList[] fields = new VarList[] { fBase, fOffset };
			final BoogieType boogieType =
					BoogieType.createStructType(new String[] { SFO.POINTER_BASE, SFO.POINTER_OFFSET },
							new BoogieType[] { (BoogieType) fBase.getType().getBoogieType(),
									(BoogieType) fOffset.getType().getBoogieType() });
			final ASTType pointerType = new StructType(tuLoc, boogieType, fields);
			// Pointer is non-finite, right? (ZxZ)..
			decl.add(new TypeDeclaration(tuLoc, new Attribute[0], false, SFO.POINTER, new String[0], pointerType));
		}
		return decl;
	}

	@Override
	public boolean areFloatingTypesNeeded() {
		return mFloatingTypesNeeded;
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
		if (type1 instanceof CStructOrUnion && type2 instanceof CStructOrUnion) {
			return areMatchingTypes(type1, type2);
		}
		return false;
	}

	@Override
	public BoogieType getBoogieTypeForBoogieASTType(final ASTType asttype) {
		if (asttype == null) {
			return BoogieType.TYPE_ERROR;
		}
		final BoogieType result = (BoogieType) asttype.getBoogieType();
		assert result != null;
		return result;
	}

	@Override
	public BoogieType getBoogieTypeForSizeT() {
		return BoogieType.TYPE_INT;
	}

	@Override
	public BoogieType getBoogieTypeForCType(final CType cTypeRaw) {
		final CType cType = cTypeRaw.getUnderlyingType();

		if (cType instanceof CPrimitive) {
			if (mTranslationSettings.isBitvectorTranslation()) {
				final Integer byteSize = mTypeSizes.getSize(((CPrimitive) cType).getType());
				return BoogieType.createBitvectorType(byteSize * 8);
			}
			switch (((CPrimitive) cType).getGeneralType()) {
			case FLOATTYPE:
				return BoogieType.TYPE_REAL;
			case INTTYPE:
				return BoogieType.TYPE_INT;
			case VOID:
				return BoogieType.TYPE_ERROR;
			default:
				throw new AssertionError();
			}
		} else if (cType instanceof CPointer) {
			return getBoogiePointerType();
		} else if (cType instanceof CEnum) {
			return getBoogieTypeForCType(new CPrimitive(CPrimitives.INT));
		} else if (cType instanceof CArray) {

			// may have to change this from int to something depending on bitvector settings and stuff..
			final BoogieType[] indexTypes =
					new BoogieType[] { getBoogieTypeForCType(new CPrimitive(CPrimitives.UINT)) };

			final BoogieType valueType = getBoogieTypeForCType(((CArray) cType).getValueType());
			return BoogieType.createArrayType(0, indexTypes, valueType);
		} else if (cType instanceof CFunction) {
			return getBoogiePointerType();
		} else if (cType instanceof CStructOrUnion) {
			final CStructOrUnion cStructType = (CStructOrUnion) cType;
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
		return mBoogiePointerType;
	}

	@Override
	public BoogieType getBoogieTypeForPointerComponents() {
		return getBoogieTypeForCType(mTranslationSettings.getCTypeOfPointerComponents());
	}

	private static boolean isCharArray(final CType cTypeRaw) {
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
				new SymbolTableValue(boogieId, cd,
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
			final Expression valueOfPrecedingEnumConstant, final IASTEnumerationSpecifier node) {
		final CPrimitive typeOfEnumIdentifiers = new CPrimitive(CPrimitive.CPrimitives.INT);
		final Expression value;
		if (specifiedValue != null) {
			// case where the value of the enumeration constant is explicitly defined by an
			// integer constant expression
			value = specifiedValue;
		} else {
			// case where the value of the enumeration constant is not explicitly defined by
			// an integer constant expression and hence the value of the preceding
			// enumeration constant in the list defines the value of this enumeration
			// constant (see C11 6.7.2.2.3)
			if (valueOfPrecedingEnumConstant == null) {
				// case where this is the first enumeration constant in the list
				final Expression zero =
						mTypeSizes.constructLiteralForIntegerType(loc, typeOfEnumIdentifiers, BigInteger.ZERO);
				value = zero;
			} else {
				final BigInteger bi =
						mTypeSizes.extractIntegerValue(valueOfPrecedingEnumConstant, typeOfEnumIdentifiers, node);
				if (bi == null) {
					throw new AssertionError("not an integer constant: " + specifiedValue);
				}
				final int valueOfPrecedingEnumConstantAsInt = bi.intValue();
				final int valueAsInt = valueOfPrecedingEnumConstantAsInt + 1;
				value = mTypeSizes.constructLiteralForIntegerType(loc, typeOfEnumIdentifiers,
						BigInteger.valueOf(valueAsInt));
			}
		}
		return value;
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

	private ASTType cPrimitive2AstType(final ILocation loc, final CPrimitive cPrimitive) {
		final BoogieType boogieType = getBoogieTypeForCType(cPrimitive);

		switch (cPrimitive.getGeneralType()) {
		case VOID:
			// (alex:) seems to be lindemm's convention, see FunctionHandler.isInParamVoid(..)
			return null;
		case INTTYPE:
			if (mTranslationSettings.isBitvectorTranslation()) {
				return new NamedType(loc, boogieType, "C_" + cPrimitive.getType().toString(), new ASTType[0]);
			}
			return new PrimitiveType(loc, boogieType, SFO.INT);
		case FLOATTYPE:
			mFloatingTypesNeeded = true;
			if (mTranslationSettings.isBitvectorTranslation()) {
				return new NamedType(loc, boogieType, "C_" + cPrimitive.getType().toString(), new ASTType[0]);
			}
			return new PrimitiveType(loc, boogieType, SFO.REAL);
		default:
			throw new UnsupportedSyntaxException(loc, "unknown primitive type");
		}
	}

	private static boolean areMatchingTypes(final CType type1, final CType type2,
			final SymmetricHashRelation<CType> visitedPairs) {

		final CType ulType1 = type1.getUnderlyingType();
		final CType ulType2 = type2.getUnderlyingType();

		if (!ulType1.getClass().equals(ulType2.getClass())) {
			return false;
		}

		if (visitedPairs.containsPair(type1, type2)) {
			// found a cycle in the c type --> types match
			return true;
		}

		if (ulType1.getClass().equals(CPrimitive.class)) {
			return areMatchingTypes((CPrimitive) ulType1, (CPrimitive) ulType2, visitedPairs);
		} else if (ulType1.getClass().equals(CEnum.class)) {
			return areMatchingTypes((CEnum) ulType1, (CEnum) ulType2, visitedPairs);
		} else if (ulType1.getClass().equals(CPointer.class)) {
			return areMatchingTypes((CPointer) ulType1, (CPointer) ulType2, visitedPairs);
		} else if (ulType1.getClass().equals(CStructOrUnion.class)) {
			return areMatchingTypes((CStructOrUnion) ulType1, (CStructOrUnion) ulType2, visitedPairs);
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

		if (!(type1.getName().equals(type2.getName()))) {
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

		visitedPairs.addPair(type1, type2);

		// function have different number of arguments
		if (type1.getParameterTypes().length != type2.getParameterTypes().length) {
			return false;
		}

		// one function takes varargs, the other does not
		if (type1.takesVarArgs() != type2.takesVarArgs()) {
			return false;
		}

		// function result types are different
		if (!areMatchingTypes(type1.getResultType(), type2.getResultType(), visitedPairs)) {
			return false;
		}

		// function parameter types are different
		for (int i = 0; i < type1.getParameterTypes().length; i++) {
			if (!areMatchingTypes(type1.getParameterTypes()[i].getType(), type2.getParameterTypes()[i].getType(),
					visitedPairs)) {
				return false;
			}
		}
		return true;
	}

	private static boolean areMatchingTypes(final CStructOrUnion type1, final CStructOrUnion type2,
			final SymmetricHashRelation<CType> visitedPairs) {

		visitedPairs.addPair(type1, type2);

		// different number of fields means structs dont match
		if (type1.getFieldIds().length != type2.getFieldIds().length) {
			return false;
		}

		// different number of field types mean structs dont match
		// DD: this looks like it should be an invariant in CStruct, or is it possible to have unnamed fields? If yes,
		// how are they matched to their type?
		if (type1.getFieldTypes().length != type2.getFieldTypes().length) {
			return false;
		}

		// TODO: DD: Do field names really impact type matching? I am not so sure that this is always the case
		for (int i = 0; i < type1.getFieldIds().length - 1; i++) {
			if (!(type1.getFieldIds()[i].equals(type2.getFieldIds()[i]))) {
				return false;
			}
		}

		// check if the types of the field match
		for (int i = 0; i < type1.getFieldTypes().length; i++) {
			if (!areMatchingTypes(type1.getFieldTypes()[i], type2.getFieldTypes()[i], visitedPairs)) {
				return false;
			}
		}
		return true;
	}

	private static boolean areMatchingTypes(final CArray type1, final CArray type2,
			final SymmetricHashRelation<CType> visitedPairs) {
		// if dimensions dont match, array dont match
		if (!type1.getBound().toString().equals(type2.getBound().toString())) {
			return false;
		}
		// compare value types
		if (!areMatchingTypes(type1.getValueType(), type2.getValueType(), visitedPairs)) {
			return false;
		}
		return true;
	}

	@Override
	public void registerNamedIncompleteType(final ICPossibleIncompleteType<?> incompleteType, final String named) {
		mNamedIncompleteTypes.addPair(incompleteType, named);
	}
}
