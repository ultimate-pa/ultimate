/*
 * Copyright 2009 Dorothea Jansen <d.jansen@uni-muenster.de>, Martin Mohr <mohrfrosch@uni-muenster.de>, Irene Thesing <i_thes01@uni-muenster.de>, Anton Reis <antonreis@gmx.de>, Maria Schatz <m_scha17@uni-muenster.de>, Philipp Claves <philipp.claves@uni-muenster.de>, Sezar Jarrous <sezar.jarrous@gmail.com>
 *
 * This file is part of LETHAL.
 *
 * LETHAL is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * LETHAL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with LETHAL.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_muenster.cs.sev.lethal.script;

import de.uni_muenster.cs.sev.lethal.script.exceptions.ScriptRuntimeError;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

/**
 * Class for simple script array list
 * Usage is Array.new(value1,value2,...)
 * @author Philipp
 *
 */
public class ArrayClass extends ScriptClass{
	
	/** Singleton ArrayClass class instance */
	public static ArrayClass arrayClass = new ArrayClass();
	
	/**
	 * Creates the array class. To be done once by the script interpreter initialization
	 * @param parentClass not used currently
	 * @param classEnvironment environment for bindings in this class.
	 */
	private ArrayClass() {
		super("Array", null, RootClass.newStaticClassEnvironment(), true);
	}

	@Override
	public ScriptObject newInstance(List<ScriptObject> args, MethodObject block) {
		ScriptObject obj = new ArrayObject(args);
		return obj;
	}
	
}

/**
 * Simple script array list object
 * @author Philipp
 *
 */
class ArrayObject extends ScriptObject{

	private List<ScriptObject> contents;
	
	/**
	 * Creates a new array instance. Only to be called by ArrayClass.newInstance
	 * @param initialEntries constructor args, initial entry content.
	 */
	public ArrayObject(List<ScriptObject> initialEntries) {
		super(ArrayClass.arrayClass);
		
		this.contents = initialEntries;
		this.setMember("add", new Method(Method.ARITY_ARBITARY){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block){
				contents.addAll(args);
				return ArrayObject.this;
			}
		});
		this.setMember("remove", new Method(Method.ARITY_ARBITARY){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block){
				contents.removeAll(args);
				return ArrayObject.this;
			}
		});
		this.setMember("remove_at", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block){
				if (args.size() != 1 || !(args.get(0) instanceof IntegerObject)) throw new ScriptRuntimeError("Array.remove_at expects integer argument");
				return contents.get(((IntegerObject)args.remove(0)).getValue());
			}
		});
		this.setMember("get", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block){
				if (args.size() != 1 || !(args.get(0) instanceof IntegerObject)) throw new ScriptRuntimeError("Array.get expects integer argument");
				return contents.get(((IntegerObject)args.get(0)).getValue());
			}
		});
		this.setMember("set", new Method(2){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block){
				if (args.size() != 2) throw new ScriptRuntimeError("Array.set expects 2 arguments");
				if (!(args.get(0) instanceof IntegerObject)) throw new ScriptRuntimeError("Array.set expects integer argument, as first argument");
				contents.set(((IntegerObject)args.get(0)).getValue(), args.get(1));
				return ArrayObject.this;
			}
		});
		this.setMember("insert", new Method(2){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block){
				if (args.size() != 2) throw new ScriptRuntimeError("Array.insert expects 2 arguments");
				if (!(args.get(0) instanceof IntegerObject)) throw new ScriptRuntimeError("Array.insert expects integer argument, as first argument");
				contents.add(((IntegerObject)args.get(0)).getValue(), args.get(1));
				return ArrayObject.this;
			}
		});
		this.setMember("size", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block){
				return ScriptObject.make(contents.size());
			}
		});
		this.setMember("contains", this.setMember("has", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block){
				if (args.size() != 1) throw new ScriptRuntimeError("Array.contains / has expects 1 argument");
				return ScriptObject.make(contents.contains(args.get(0)));
			}
		}));
		this.setMember("empty", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block){
				return ScriptObject.make(contents.isEmpty());
			}
		});
		this.setMember("each", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block){
				if (block == null) throw new ScriptRuntimeError("Array.each needs a block. e.g .each(){|item| ... }");
				List<ScriptObject> blockArgs = new ArrayList<ScriptObject>(1);
				blockArgs.add(null); //dummy for set() to work.
				ScriptObject ret = ScriptObject.nullValue;
				for (ScriptObject item : contents){
					blockArgs.set(0, item);
					ret = block.call(blockArgs,null);
				}
				return ret;
			}
		});
		this.setMember("each_rev", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block){
				if (block == null) throw new ScriptRuntimeError("Array.each needs a block. e.g .each(){|item| ... }");
				List<ScriptObject> blockArgs = new ArrayList<ScriptObject>(1);
				blockArgs.add(null); //dummy for set() to work.
				ScriptObject ret = ScriptObject.nullValue;
				for (int i = contents.size() - 1; i >= 0; i--){
					blockArgs.set(0, contents.get(i));
					ret = block.call(blockArgs,null);
				}
				return ret;
			}
		});
		this.setMember("collect", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				if (block == null) throw new ScriptRuntimeError("Array.collect needs a block. e.g .collect(){|item| ... }");
				List<ScriptObject> result = new ArrayList<ScriptObject>(contents.size());
				List<ScriptObject> blockArgs = new ArrayList<ScriptObject>(1);
				blockArgs.add(null);
				for (ScriptObject obj : contents){
					blockArgs.set(0, obj);
					result.add(block.call(blockArgs, null));
				}
				return new ArrayObject(result);
			}
		});
		this.setMember("select", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				if (block == null) throw new ScriptRuntimeError("Array.select needs a block. e.g .select(){|item| ... }");
				List<ScriptObject> result = new ArrayList<ScriptObject>();
				List<ScriptObject> blockArgs = new ArrayList<ScriptObject>(1);
				blockArgs.add(null);
				for (ScriptObject obj : contents){
					blockArgs.set(0, obj);
					if (block.call(blockArgs, null).isTrue()) result.add(obj);
				}
				return new ArrayObject(result);
			}
		});
		this.setMember("reject", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				if (block == null) throw new ScriptRuntimeError("Array.reject needs a block. e.g .reject(){|item| ... }");
				List<ScriptObject> result = new ArrayList<ScriptObject>();
				List<ScriptObject> blockArgs = new ArrayList<ScriptObject>(1);
				blockArgs.add(null);
				for (ScriptObject obj : contents){
					blockArgs.set(0, obj);
					if (!block.call(blockArgs, null).isTrue()) result.add(obj);
				}
				return new ArrayObject(result);
			}
		});
		
		this.setMember("*", this.setMember("intersect", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block){
				if (args.size() != 1 || !(args.get(0) instanceof ArrayObject)) throw new ScriptRuntimeError("Array.intersect expects another array as parameter");
				List<ScriptObject> contents2 = ((ArrayObject)args.get(0)).contents;
				List<ScriptObject> result = new ArrayList<ScriptObject>();
				for (ScriptObject obj : contents){
					if (contents2.contains(obj)) result.add(obj);
				}
				return new ArrayObject(result);
			}
		}));
		this.setMember("+", this.setMember("union", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block){
				if (args.size() != 1 || !(args.get(0) instanceof ArrayObject)) throw new ScriptRuntimeError("Array.union / + expect another array as parameter");
				List<ScriptObject> contents2 = ((ArrayObject)args.get(0)).contents;
				List<ScriptObject> result = new ArrayList<ScriptObject>(contents.size() + contents2.size());
				result.addAll(contents);
				result.addAll(contents2);
				return new ArrayObject(result);
			}			
		}));
		
		this.setMember("-", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				if (args.size() != 1 || !(args.get(0) instanceof ArrayObject)) throw new ScriptRuntimeError("Array - expects Array on right side.");
				List<ScriptObject> contents2 = ((ArrayObject)args.get(0)).contents;
				List<ScriptObject> result = new ArrayList<ScriptObject>();
				for (ScriptObject o : contents){
					if (!contents2.contains(o)) result.add(o);
				}
				return new ArrayObject(result);
			}
		});
		
		this.setMember("sort", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block){
				List<ScriptObject> content = new ArrayList<ScriptObject>();
				content.addAll(ArrayObject.this.contents);
				Collections.sort(content, new Comparator<ScriptObject>(){

					@Override
					public int compare(ScriptObject o1, ScriptObject o2) {
						List<ScriptObject> argArray = new ArrayList<ScriptObject>(1);
						argArray.add(o2);
						boolean le = o1.getMethod("<=").execute(o1.getEnvironment(), argArray, null) == ScriptObject.trueValue;
						if (!le) return 1;
						
						argArray.add(o1);
						boolean ge = o2.getMethod("<=").execute(o1.getEnvironment(), argArray, null) == ScriptObject.trueValue;
						if (!ge) return -1;
						
						return 0;
					}
					
				});
				return new ArrayObject(content);
			}
		});
		
		
	}
	
	@Override
	public String toString(){
		return contents.toString();
	}
	
	@Override
	public boolean equals(Object o){
		if (!(o instanceof ArrayObject)) return false;
		return ((ArrayObject)o).contents.equals(this.contents);
	}
	
	/**
	 * returns the list of the elements contained in this ArrayObject.
	 * @return the list of the elements contained in this ArrayObject.
	 */
	public List<ScriptObject> getContent(){
		return this.contents;
	}
	
	@Override
	public int hashCode(){
		return this.contents.hashCode();
	}
}
