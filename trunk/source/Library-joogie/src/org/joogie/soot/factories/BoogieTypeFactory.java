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

package org.joogie.soot.factories;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map.Entry;

import org.joogie.boogie.expressions.Variable;
import org.joogie.boogie.types.ArrArrayType;
import org.joogie.boogie.types.BoogieArrayType;
import org.joogie.boogie.types.BoogieBaseTypes;
import org.joogie.boogie.types.BoogieFieldType;
import org.joogie.boogie.types.BoogieObjectType;
import org.joogie.boogie.types.BoogiePrimitiveType;
import org.joogie.boogie.types.BoogieType;
import org.joogie.boogie.types.RefArrayType;
import org.joogie.util.Log;

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
 */
public class BoogieTypeFactory {

	private static HashMap<Type, BoogieType> collectedTypes = new HashMap<Type, BoogieType>();
	private static HashMap<BoogieType, BoogieFieldType> fieldTypes = new HashMap<BoogieType, BoogieFieldType>();
	private static HashMap<BoogieType, BoogieArrayType> arrayTypes = new HashMap<BoogieType, BoogieArrayType>();


	private static TypeHierarchy typeHierarchy = new TypeHierarchy();

	public static void resetFactory() {
		typeHierarchy = new TypeHierarchy();
		collectedTypes = new HashMap<Type, BoogieType>();
		fieldTypes = new HashMap<BoogieType, BoogieFieldType>();
		arrayTypes = new HashMap<BoogieType, BoogieArrayType>();
	}

	// returns -1 if a is subclass of b, 1 if b is subclass of a, 0 otherwise
	public static int compareTypes(RefType a, RefType b) {
		return typeHierarchy.compareTypes(a, b);
	}

	public static int compareTypes(BoogieType a, BoogieType b) {
		return typeHierarchy.compareTypes(a, b);
	}

	public static BoogieType lookupBoogieArrayType(ArrayType t) {
		BoogieType bt = lookupBoogieType(t.getArrayElementType());
		if (!arrayTypes.containsKey(bt)) {
			BoogieArrayType newtype = null;
			if (bt == BoogieBaseTypes.getIntType()) {
				newtype = BoogieBaseTypes.getIntArrType();
			} else if (bt == BoogieBaseTypes.getRealType()) {
				newtype = BoogieBaseTypes.getRealArrType();
			} else if (bt instanceof BoogieObjectType) {
				newtype = new RefArrayType("refarr", bt);
			} else if (bt instanceof BoogieArrayType) {
				BoogieArrayType arrt = (BoogieArrayType) bt;
				newtype = new ArrArrayType("arrarr", arrt);
			} else {
				Log.error("ERROR - Case not implemented: " + bt.toString());
				Log.error("      - maybe reflections are not handeled");
				// newtype = BoogieTypeFactory.getRefType();
			}
			arrayTypes.put(bt, newtype);
		}
		return arrayTypes.get(bt);
	}

	public static BoogieType lookupBoogieFieldType(Type t) {
		BoogieType bt = lookupBoogieType(t);
		if (!fieldTypes.containsKey(bt)) {
			fieldTypes.put(bt, new BoogieFieldType("field", bt));
		}
		return fieldTypes.get(bt);
	}

	public static BoogieType lookupBoogieType(Type t) {
		if (!collectedTypes.containsKey(t)) {
			collectedTypes.put(t, createBoogieType(t));
		}
		return collectedTypes.get(t);
	}

	private static BoogieType createBoogieType(Type t) {
		BoogieType ret = null;
		if (t instanceof PrimType) {
			ret = lookupPrimitiveType((PrimType) t);
		} else if (t instanceof RefType) {
			ret = typeHierarchy.lookupType((RefType) t);
		} else if (t instanceof ArrayType) {
			ret = lookupBoogieArrayType((ArrayType) t);
		} else if (t == NullType.v()) {
			ret = BoogieBaseTypes.getRefType();
		} else if (t instanceof VoidType) {
			ret = BoogieBaseTypes.getVoidType();
		} else {
			Log.error("Unknown Type " + t.toString()
					+ ": BoogieTypeFactory.lookupPrimitiveType");
			ret = null;
		}
		return ret;
	}

	private static BoogiePrimitiveType lookupPrimitiveType(PrimType t) {
		BoogiePrimitiveType ret = null;
		if (t instanceof DoubleType || t instanceof FloatType) {
			ret = BoogieBaseTypes.getRealType();
		} else if (t instanceof IntType || t instanceof LongType
				|| t instanceof ByteType || t instanceof CharType
				|| t instanceof ShortType || t instanceof BooleanType) {
			ret = BoogieBaseTypes.getIntType();
		} else {
			Log.error("Unknown PrimType " + t.toString()
					+ ": BoogieTypeFactory.lookupPrimitiveType");
			ret = new BoogiePrimitiveType("PTYPENOTKNOWN" + t.toString());
		}
		return ret;
	}

	public static Variable createTypeVariable(RefType t) {
		return typeHierarchy.createTypeVariable(t);
	}


	private static class TypeHierarchy {
		private HashMap<RefType, TypeNode> usedTypes = new HashMap<RefType, TypeNode>();
		private HashMap<BoogieType, TypeNode> boogie2Nodes = new HashMap<BoogieType, TypeNode>();

		// TypeNode rootNode = null;

		public Variable createTypeVariable(RefType t) {
			if (!usedTypes.containsKey(t)) {
				registerType(t);
			}
			TypeNode tn = usedTypes.get(t);
			Variable v = new Variable(tn.ClassName, BoogieBaseTypes.getClassConstType(), false);
			return v;
		}

		public int compareTypes(RefType a, RefType b) {
			if (!usedTypes.containsKey(a)) {
				registerType(a);
			}
			if (!usedTypes.containsKey(b)) {
				registerType(b);
			}
			TypeNode n1 = usedTypes.get(a);
			TypeNode n2 = usedTypes.get(b);
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
			if (!usedTypes.containsKey(t)) {
				registerType(t);
			}
			return usedTypes.get(t).Value;
		}

		public TypeNode registerType(RefType t) {
			TypeNode ret = null;
			if (usedTypes.containsKey(t)) {
				return usedTypes.get(t);
			} else {
				if (t.getSootClass().hasSuperclass()) {
					TypeNode supertype = registerType(t.getSootClass()
							.getSuperclass().getType());
					ret = new TypeNode(((RefType) t).getClassName());
					String shortname = t.getSootClass().getShortName()
							+ t.getNumber();
					ret.Value = new BoogieObjectType(shortname);
					ret.Parent = supertype;
					supertype.Children.add(ret);
					usedTypes.put(t, ret);
					boogie2Nodes.put(ret.Value, ret);
					return ret;
				} else {
					ret = new TypeNode(((RefType) t).getClassName());
					ret.Value = new BoogieObjectType(
							((RefType) t).getClassName());
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

		private class TypeNode {
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
