package de.uni_freiburg.informatik.ultimate.boogie.preprocessor;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.ListIterator;
import java.util.Stack;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.type.TypeConstructor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.TypeDeclaration;

public class TypeManager {

	private Logger mLogger;

	private HashMap<String, TypeConstructor> typeConstructors = new HashMap<String, TypeConstructor>();
	private HashMap<String, TypeDeclaration> declarations = new HashMap<String, TypeDeclaration>();
	private Stack<String> visiting = new Stack<String>();
	private Stack<TypeParameters> typeParamScopes = new Stack<TypeParameters>();

	public TypeManager(Declaration[] decls, Logger logger) {
		mLogger = logger;
		for (Declaration d : decls) {
			if (d instanceof TypeDeclaration) {
				TypeDeclaration td = (TypeDeclaration) d;
				declarations.put(td.getIdentifier(), td);
			}
		}
	}

	public void pushTypeScope(TypeParameters typeParams) {
		typeParamScopes.push(typeParams);
	}

	public void popTypeScope() {
		typeParamScopes.pop();
	}

	public BoogieType getPrimitiveType(String typeName) {
		if (typeName.equals("int"))
			return BoogieType.intType;
		else if (typeName == "real")
			return BoogieType.realType;
		else if (typeName == "bool")
			return BoogieType.boolType;
		else if (typeName.startsWith("bv")) {
			int length = Integer.parseInt(typeName.substring(2));
			return BoogieType.createBitvectorType(length);
		} else {
			mLogger.fatal("getPrimitiveType called with unknown type " + typeName + "!");
			return BoogieType.errorType;
		}
	}

	public BoogieType resolveNamedType(NamedType type, boolean markUsed) {
		String name = type.getName();
		int numParam = type.getTypeArgs().length;

		ListIterator<TypeParameters> it = typeParamScopes.listIterator(typeParamScopes.size());
		int increment = 0;
		while (it.hasPrevious()) {
			TypeParameters tp = it.previous();
			BoogieType placeholderType = tp.findType(name, increment, markUsed);
			if (placeholderType != null) {
				if (numParam != 0) {
					mLogger.error("Bounded type " + name + " used with arguments.");
					return BoogieType.errorType;
				}
				return placeholderType;
			}
			increment += tp.getCount();
		}

		if (!typeConstructors.containsKey(name)) {
			TypeDeclaration decl = declarations.get(name);
			if (decl == null) {
				mLogger.error("Type " + name + " is never defined.");
				return BoogieType.errorType;
			}
			resolve(decl);
		}
		TypeConstructor tc = typeConstructors.get(name);
		if (tc == null) /* cyclic definition, already reported */
			return BoogieType.errorType;

		if (tc.getParamCount() != numParam) {
			mLogger.error("Type " + name + " used with wrong number of arguments.");
			return BoogieType.errorType;
		}
		BoogieType[] typeArgs = new BoogieType[numParam];
		for (int i : tc.getParamOrder()) {
			typeArgs[i] = resolveType(type.getTypeArgs()[i], markUsed);
		}
		for (int i = 0; i < numParam; i++) {
			/*
			 * Resolve the other type arguments without marking place holders as
			 * used. Place holders are actually instantiated as tError.
			 */
			if (typeArgs[i] == null)
				typeArgs[i] = resolveType(type.getTypeArgs()[i], false);
		}
		return BoogieType.createConstructedType(tc, typeArgs);
	}

	public BoogieType resolveArrayType(ArrayType type, boolean markUsed) {
		TypeParameters typeParams = new TypeParameters(type.getTypeParams());
		pushTypeScope(typeParams);
		int numIndices = type.getIndexTypes().length;
		BoogieType[] indexTypes = new BoogieType[numIndices];
		for (int i = 0; i < numIndices; i++) {
			indexTypes[i] = resolveType(type.getIndexTypes()[i], markUsed);
		}
		if (!typeParams.fullyUsed())
			mLogger.error("ArrayType generics not used in index types: " + type);
		BoogieType resultType = resolveType(type.getValueType(), markUsed);
		popTypeScope();

		return BoogieType.createArrayType(type.getTypeParams().length, indexTypes, resultType);
	}

	private BoogieType resolveStructType(StructType type, boolean markUsed) {
		ArrayList<String> names = new ArrayList<String>(type.getFields().length);
		ArrayList<BoogieType> types = new ArrayList<BoogieType>(type.getFields().length);

		for (int i = 0; i < type.getFields().length; i++) {
			BoogieType fieldType = resolveType(type.getFields()[i].getType(), markUsed);
			for (String id : type.getFields()[i].getIdentifiers()) {
				names.add(id);
				types.add(fieldType);
			}
		}
		String[] fNames = names.toArray(new String[names.size()]);
		BoogieType[] fTypes = types.toArray(new BoogieType[types.size()]);
		return BoogieType.createStructType(fNames, fTypes);
	}

	public BoogieType resolveType(ASTType type, boolean markUsed) {
		BoogieType boogieType;
		if (type instanceof PrimitiveType)
			boogieType = getPrimitiveType(((PrimitiveType) type).getName());
		else if (type instanceof NamedType)
			boogieType = resolveNamedType((NamedType) type, markUsed);
		else if (type instanceof ArrayType)
			boogieType = resolveArrayType((ArrayType) type, markUsed);
		else if (type instanceof StructType)
			boogieType = resolveStructType((StructType) type, markUsed);
		else {
			mLogger.fatal("Unknown ASTType " + type);
			boogieType = BoogieType.errorType;
		}
		type.setBoogieType(boogieType);
		return boogieType;
	}

	public BoogieType resolveType(ASTType type) {
		return resolveType(type, true);
	}

	public void resolve(TypeDeclaration td) {
		if (visiting.contains(td.getIdentifier())) {
			mLogger.fatal("Cyclic type definition: " + visiting);
			typeConstructors.put(td.getIdentifier(), null);
		}
		visiting.push(td.getIdentifier());
		String name = td.getIdentifier();
		String[] typeParams = td.getTypeParams();
		BoogieType synonym = null;
		int[] order;
		if (td.getSynonym() != null) {
			TypeParameters tp = new TypeParameters(typeParams, true);
			pushTypeScope(tp);
			synonym = resolveType(td.getSynonym());
			order = new int[tp.getNumUsed()];
			System.arraycopy(tp.getOrder(), 0, order, 0, order.length);
			popTypeScope();
		} else {
			order = new int[typeParams.length];
			for (int i = 0; i < order.length; i++)
				order[i] = i;
		}
		visiting.pop();
		typeConstructors.put(name, new TypeConstructor(name, td.isFinite(), typeParams.length, order, synonym));
	}

	public void init() {
		for (TypeDeclaration td : declarations.values()) {
			if (typeConstructors.containsKey(td.getIdentifier()))
				continue;
			resolve(td);
		}
	}

}
