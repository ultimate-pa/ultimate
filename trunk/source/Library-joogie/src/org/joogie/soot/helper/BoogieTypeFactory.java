/*
 * Joogie translates Java bytecode to the Boogie intermediate verification language
 * Copyright (C) 2011 Martin Schaef and Stephan Arlt
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
 */

package org.joogie.soot.helper;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.joogie.boogie.expressions.Variable;
import org.joogie.boogie.types.ArrArrayType;
import org.joogie.boogie.types.BoogieArrayType;
import org.joogie.boogie.types.BoogiePreludeTypes;
import org.joogie.boogie.types.BoogieFieldType;
import org.joogie.boogie.types.BoogieObjectType;
import org.joogie.boogie.types.BoogiePrimitiveType;
import org.joogie.boogie.types.BoogieType;
import org.joogie.boogie.types.RefArrayType;

import soot.ArrayType;
import soot.BooleanType;
import soot.ByteType;
import soot.CharType;
import soot.DoubleType;
import soot.FloatType;
import soot.IntType;
import soot.LongType;
import soot.NullType;
import soot.PrimType;
import soot.RefType;
import soot.ShortType;
import soot.Type;
import soot.VoidType;

/**
 * Only a stub
 * 
 * @author schaef
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * 
 */
public class BoogieTypeFactory {

	private final Map<Type, BoogieType> mCollectedTypes;
	private final Map<BoogieType, BoogieFieldType> mFieldTypes;
	private final Map<BoogieType, BoogieArrayType> mArrayTypes;
	private final TypeHierarchy mTypeHierarchy;

	BoogieTypeFactory() {
		mCollectedTypes = new HashMap<Type, BoogieType>();
		mFieldTypes = new HashMap<BoogieType, BoogieFieldType>();
		mArrayTypes = new HashMap<BoogieType, BoogieArrayType>();
		mTypeHierarchy = new TypeHierarchy();
	}

	/**
	 * @return -1 if a is subclass of b, 1 if b is subclass of a, 0 otherwise
	 */
	public int compareTypes(RefType a, RefType b) {
		return mTypeHierarchy.compareTypes(a, b);
	}

	public int compareTypes(BoogieType a, BoogieType b) {
		return mTypeHierarchy.compareTypes(a, b);
	}

	public BoogieType lookupBoogieArrayType(ArrayType t) {
		final BoogieType bt = lookupBoogieType(t.getArrayElementType());
		BoogieArrayType newtype = mArrayTypes.get(bt);
		if (newtype == null) {
			if (bt == BoogiePreludeTypes.TYPE_INT) {
				newtype = BoogiePreludeTypes.TYPE_INT_ARRAY;
			} else if (bt == BoogiePreludeTypes.TYPE_REAL) {
				newtype = BoogiePreludeTypes.TYPE_REAL_ARRAY;
			} else if (bt instanceof BoogieObjectType) {
				newtype = new RefArrayType("refarr", bt);
			} else if (bt instanceof BoogieArrayType) {
				BoogieArrayType arrt = (BoogieArrayType) bt;
				newtype = new ArrArrayType("arrarr", arrt);
			} else {
				// newtype = BoogieTypeFactory.getRefType();
				throw new UnsupportedOperationException("Case not implemented (maybe reflections?): " + bt.toString());
			}
			mArrayTypes.put(bt, newtype);
		}
		return newtype;
	}

	public BoogieType lookupBoogieFieldType(Type t) {
		BoogieType bt = lookupBoogieType(t);
		BoogieFieldType ftype = mFieldTypes.get(bt);
		if (ftype == null) {
			ftype = new BoogieFieldType(BoogiePreludeTypes.TYPE_FIELD.getName(), bt);
			mFieldTypes.put(bt, ftype);
		}
		return ftype;
	}

	public BoogieType lookupBoogieType(Type t) {
		if (!mCollectedTypes.containsKey(t)) {
			mCollectedTypes.put(t, createBoogieType(t));
		}
		return mCollectedTypes.get(t);
	}

	private BoogieType createBoogieType(Type t) {
		BoogieType ret = null;
		if (t instanceof PrimType) {
			ret = lookupPrimitiveType((PrimType) t);
		} else if (t instanceof RefType) {
			ret = mTypeHierarchy.lookupType((RefType) t);
		} else if (t instanceof ArrayType) {
			ret = lookupBoogieArrayType((ArrayType) t);
		} else if (t == NullType.v()) {
			ret = BoogiePreludeTypes.TYPE_REF;
		} else if (t instanceof VoidType) {
			ret = BoogiePreludeTypes.TYPE_VOID;
		} else {
			ret = null;
			throw new UnsupportedOperationException(
					"Unknown Type " + t.toString() + ": BoogieTypeFactory.lookupPrimitiveType");
		}
		return ret;
	}

	private BoogiePrimitiveType lookupPrimitiveType(PrimType t) {
		BoogiePrimitiveType ret = null;
		if (t instanceof DoubleType || t instanceof FloatType) {
			ret = BoogiePreludeTypes.TYPE_REAL;
		} else if (t instanceof IntType || t instanceof LongType || t instanceof ByteType || t instanceof CharType
				|| t instanceof ShortType || t instanceof BooleanType) {
			ret = BoogiePreludeTypes.TYPE_INT;
		} else {
			throw new UnsupportedOperationException(
					"Unknown PrimType " + t.toString() + ": BoogieTypeFactory.lookupPrimitiveType");
		}
		return ret;
	}

	public Variable createTypeVariable(RefType t) {
		return mTypeHierarchy.createTypeVariable(t);
	}

	private static final class TypeHierarchy {
		private HashMap<RefType, TypeNode> usedTypes = new HashMap<RefType, TypeNode>();
		private HashMap<BoogieType, TypeNode> boogie2Nodes = new HashMap<BoogieType, TypeNode>();

		public Variable createTypeVariable(RefType t) {
			final TypeNode tn = getTypeNode(t);
			return new Variable(tn.ClassName, BoogiePreludeTypes.TYPE_CLASS_CONST, false);
		}

		private TypeNode getTypeNode(RefType type) {
			TypeNode rtr = usedTypes.get(type);
			if (rtr == null) {
				rtr = registerType(type);
			}
			assert rtr != null;
			return rtr;
		}

		public int compareTypes(RefType a, RefType b) {
			TypeNode n1 = getTypeNode(a);
			TypeNode n2 = getTypeNode(b);
			List<TypeNode> par_n1 = collectParents(n1);
			List<TypeNode> par_n2 = collectParents(n2);
			if (par_n1.contains(n2)) {
				return -1;
			} else if (par_n2.contains(n1)) {
				return 1;
			}
			return 0;
		}

		public int compareTypes(BoogieType a, BoogieType b) {
			TypeNode n1 = boogie2Nodes.get(a);
			TypeNode n2 = boogie2Nodes.get(b);
			List<TypeNode> par_n1 = collectParents(n1);
			List<TypeNode> par_n2 = collectParents(n2);
			if (par_n1.contains(n2)) {
				return -1;
			} else if (par_n2.contains(n1)) {
				return 1;
			}
			return 0;
		}

		private List<TypeNode> collectParents(TypeNode n) {
			ArrayList<TypeNode> ret = new ArrayList<TypeNode>();
			TypeNode cur = n;
			while (cur != null) {
				ret.add(cur);
				cur = cur.Parent;
			}
			return ret;
		}

		public BoogieType lookupType(RefType t) {
			return getTypeNode(t).Value;
		}

		public TypeNode registerType(RefType t) {
			TypeNode ret = null;
			if (usedTypes.containsKey(t)) {
				return usedTypes.get(t);
			} else {
				if (t.getSootClass().hasSuperclass()) {
					TypeNode supertype = registerType(t.getSootClass().getSuperclass().getType());
					ret = new TypeNode(((RefType) t).getClassName());
					// String shortname = t.getSootClass().getShortName() +
					// t.getNumber();
					// ret.Value = new BoogieObjectType(shortname);
					ret.Value = BoogiePreludeTypes.TYPE_REF;
					ret.Parent = supertype;
					supertype.Children.add(ret);
					usedTypes.put(t, ret);
					boogie2Nodes.put(ret.Value, ret);
					return ret;
				} else {
					ret = new TypeNode(((RefType) t).getClassName());
					// ret.Value = new BoogieObjectType(((RefType)
					// t).getClassName());
					ret.Value = BoogiePreludeTypes.TYPE_REF;
					usedTypes.put(t, ret);
					boogie2Nodes.put(ret.Value, ret);
					// rootNode = ret;
					return ret;
				}
			}
		}

		public String toString() {
			StringBuilder sb = new StringBuilder();
			for (Entry<RefType, TypeNode> e : usedTypes.entrySet()) {
				sb.append(e.getValue().toString() + "\n");
			}
			return sb.toString();
		}

		private static class TypeNode {
			public TypeNode Parent = null;
			public List<TypeNode> Children = new ArrayList<TypeNode>();
			public BoogieType Value = null;
			public String ClassName;

			public TypeNode(String cn) {
				ClassName = cn;
			}

			public String toString() {
				StringBuilder sb = new StringBuilder();
				sb.append(Value.toBoogie());
				TypeNode cur = Parent;
				while (cur != null) {
					sb.append(" :> ");
					sb.append(cur.Value.toBoogie());
					cur = cur.Parent;
				}
				return sb.toString();
			}
		}
	}

}
