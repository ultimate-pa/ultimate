package de.uni_freiburg.informatik.ultimate.boogie.type;

import java.util.ArrayList;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;

public class StructExpanderUtil {

	public static final String ATTRIBUTE_EXPAND_STRUCT = "expand_struct";

	/**
	 * don't instantiate
	 */
	private StructExpanderUtil() {

	}

	/**
	 * String holding a period / dot.
	 */
	public static final String DOT = ".";

	/**
	 * Create a new struct wrapper type and register the corresponding type constructor, unless that is already present.
	 * The input type must already be flattened, i.e., the field types do not contain any structs.
	 *
	 * @param st
	 *            the struct type for which a wrapper is created.
	 * @returns a new constructed type for this struct type.
	 */
	public static BoogieType createStructWrapperType(final BoogieStructType st,
			final Map<String, BoogieTypeConstructor> structTypes) {
		final StringBuilder sb = new StringBuilder();
		sb.append("struct");
		for (final String f : st.getFieldIds()) {
			sb.append('~').append(f);
		}
		final String name = sb.toString();
		BoogieTypeConstructor tc = structTypes.get(name);
		if (tc == null) {
			final int[] paramOrder = new int[st.getFieldCount()];
			for (int i = 0; i < paramOrder.length; i++) {
				paramOrder[i] = i;
			}
			tc = new BoogieTypeConstructor(name, false, st.getFieldCount(), paramOrder);
			structTypes.put(name, tc);
		}
		final BoogieType[] types = new BoogieType[st.getFieldCount()];
		for (int i = 0; i < types.length; i++) {
			types[i] = st.getFieldType(i);
		}
		return BoogieType.createConstructedType(tc, types);
	}

	/**
	 * Convert a type to a flattened type, where there is a single struct type at the outside. arrays of structs are
	 * converted to structs of arrays and nested structs are flattened. We work on BoogieType and use
	 * getUnderlyingType() so that we do not need to handle type aliases.
	 *
	 * @param itype
	 *            the type that should be flattened. This must be a BoogieType, but we want to avoid casts everywhere.
	 * @param structTypes
	 * @return the flattened type as BoogieType.
	 */
	public static BoogieType flattenType(final IBoogieType itype, final Map<BoogieType, BoogieType> flattenCache,
			final Map<String, BoogieTypeConstructor> structTypes) {
		BoogieType result;
		final BoogieType type = ((BoogieType) itype).getUnderlyingType();
		if (flattenCache.containsKey(type)) {
			return flattenCache.get(type);
		}
		if (type instanceof BoogiePrimitiveType) {
			result = type;
		} else if (type instanceof BoogieConstructedType) {
			final BoogieConstructedType ctype = (BoogieConstructedType) type;
			final int numParams = ctype.getParameterCount();
			final BoogieType[] paramTypes = new BoogieType[numParams];
			for (int i = 0; i < paramTypes.length; i++) {
				paramTypes[i] = flattenType(ctype.getParameter(i), flattenCache, structTypes);
				if (paramTypes[i] instanceof BoogieStructType) {
					final BoogieStructType st = (BoogieStructType) paramTypes[i];
					paramTypes[i] = createStructWrapperType(st, structTypes);
				}
			}
			result = BoogieType.createConstructedType(ctype.getConstr(), paramTypes);
		} else if (type instanceof BoogieArrayType) {
			final BoogieArrayType at = (BoogieArrayType) type;
			final ArrayList<BoogieType> flattenedIndices = new ArrayList<>();
			for (int i = 0; i < at.getIndexCount(); i++) {
				final BoogieType flat = flattenType(at.getIndexType(i), flattenCache, structTypes);
				if (flat instanceof BoogieStructType) {
					final BoogieStructType st = (BoogieStructType) flat;
					for (int j = 0; j < st.getFieldCount(); j++) {
						flattenedIndices.add(st.getFieldType(j));
					}
				} else {
					flattenedIndices.add(flat);
				}
			}
			final BoogieType[] indexTypes = flattenedIndices.toArray(new BoogieType[flattenedIndices.size()]);
			final BoogieType valueType = flattenType(at.getValueType(), flattenCache, structTypes);
			if (valueType instanceof BoogieStructType) {
				final BoogieStructType st = (BoogieStructType) valueType;
				final String[] names = st.getFieldIds();
				final BoogieType[] resultTypes = new BoogieType[names.length];
				for (int i = 0; i < names.length; i++) {
					resultTypes[i] =
							BoogieType.createArrayType(at.getNumPlaceholders(), indexTypes, st.getFieldType(i));
				}
				result = BoogieType.createStructType(names, resultTypes);
			} else {
				result = BoogieType.createArrayType(at.getNumPlaceholders(), indexTypes, valueType);
			}
		} else if (type instanceof BoogieStructType) {
			final BoogieStructType stype = (BoogieStructType) type;
			final ArrayList<String> allNames = new ArrayList<>();
			final ArrayList<BoogieType> allTypes = new ArrayList<>();
			for (int i = 0; i < stype.getFieldCount(); i++) {
				final String id = stype.getFieldIds()[i];
				final BoogieType bt = flattenType(stype.getFieldType(i), flattenCache, structTypes);
				if (bt instanceof BoogieStructType) {
					final BoogieStructType st = (BoogieStructType) bt;
					for (int j = 0; j < st.getFieldCount(); j++) {
						allNames.add(id + DOT + st.getFieldIds()[j]);
						allTypes.add(st.getFieldType(j));
					}
				} else {
					allNames.add(id);
					allTypes.add(bt);
				}
			}
			final String[] names = allNames.toArray(new String[allNames.size()]);
			final BoogieType[] types = allTypes.toArray(new BoogieType[allTypes.size()]);
			result = BoogieType.createStructType(names, types);
		} else if (type instanceof BoogiePlaceholderType) {
			result = type;
		} else {
			throw new AssertionError("Unknown ASTType " + type);
		}
		flattenCache.put(type, result);
		return result;
	}

}
