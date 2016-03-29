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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import de.uni_muenster.cs.sev.lethal.script.exceptions.ScriptRuntimeError;

/**
 * Simple Hash map wrapper class
 * @author Philipp
 *
 */
public class HashClass extends ScriptClass {

	/** Singleton HashClass class instance */
	public static final HashClass hashClass = new HashClass();
	
	private HashClass() {
		super("Hash", null, RootClass.newStaticClassEnvironment(), true);
	}

	@Override
	public ScriptObject newInstance(List<ScriptObject> args, MethodObject block) {
		if ((args.size() & 1) != 0) throw new ScriptRuntimeError("Hash.new expects an even number of arguments (key, value pairs)");
		HashMap<ScriptObject,ScriptObject> content = new HashMap<ScriptObject,ScriptObject>(args.size() / 2);
		for (int i = 0; i < args.size(); i+=2){
			content.put(args.get(i), args.get(i+1));
		}
		return new HashObject(content);
	}

}

/**
 * Hash object class.
 * Wraps a HashMap for script usage 
 * @author Philipp
 *
 */
class HashObject extends ScriptObject {

	private HashMap<ScriptObject,ScriptObject> contents;
	
	public HashObject(final HashMap<ScriptObject,ScriptObject> contents) {
		super(HashClass.hashClass);
		this.contents = contents;
		this.setMember("set", this.setMember("put", new Method(2){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block){
				contents.put(args.get(0), args.get(1));
				return HashObject.this;
			}
		}));
		this.setMember("remove", new Method(Method.ARITY_ARBITARY){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block){
				for (ScriptObject key : args){
					contents.remove(key);
				}
				return HashObject.this;
			}
		});
		this.setMember("get", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block){
				if (args.size() != 1 ) throw new ScriptRuntimeError("Hash.get expects 1 argument");
				return ScriptObject.maskNull(contents.get(args.get(0)));
			}
		});

		this.setMember("size", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block){
				return ScriptObject.make(contents.size());
			}
		});
		this.setMember("contains_key", this.setMember("has_key", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block){
				return ScriptObject.make(contents.containsKey(args.get(0)));
			}
		}));
		this.setMember("contains_value", this.setMember("has_value", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block){
				return ScriptObject.make(contents.containsValue(args.get(0)));
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
				if (block == null) throw new ScriptRuntimeError("Hash.each needs a block. e.g .each(){|key,value| ... }");
				List<ScriptObject> blockArgs = new ArrayList<ScriptObject>(2);
				blockArgs.add(null); //dummy for set() to work.
				blockArgs.add(null); //dummy for set() to work.
				ScriptObject ret = ScriptObject.nullValue;
				for (ScriptObject key : contents.keySet()){
					blockArgs.set(0, key);
					blockArgs.set(1, contents.get(key));
					ret = block.call(blockArgs,null);
				}
				return ret;
			}
		});
		this.setMember("each_key", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block){
				if (block == null) throw new ScriptRuntimeError("Hash.each needs a block. e.g .each(){|key,value| ... }");
				List<ScriptObject> blockArgs = new ArrayList<ScriptObject>(1);
				blockArgs.add(null); //dummy for set() to work.
				ScriptObject ret = ScriptObject.nullValue;
				for (ScriptObject key : contents.keySet()){
					blockArgs.set(0, key);
					ret = block.call(blockArgs,null);
				}
				return ret;
			}
		});
		this.setMember("each_value", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block){
				if (block == null) throw new ScriptRuntimeError("Hash.each needs a block. e.g .each(){|key,value| ... }");
				List<ScriptObject> blockArgs = new ArrayList<ScriptObject>(2);
				blockArgs.add(null); //dummy for set() to work.
				ScriptObject ret = ScriptObject.nullValue;
				for (ScriptObject value : contents.values()){
					blockArgs.set(1, value);
					ret = block.call(blockArgs,null);
				}
				return ret;
			}
		});
	}
	
	public HashMap<ScriptObject,ScriptObject> getContent(){
		return this.contents;
	}
	
	@Override
	public String toString(){
		return contents.toString();
	}
	
	@Override
	public boolean equals(Object o){
		if (!(o instanceof ArrayObject)) return false;
		return ((ArrayObject)o).getContent().equals(this.contents);
	}
	
	@Override
	public int hashCode(){
		return this.contents.hashCode();
	}
	
}
