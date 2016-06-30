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
import java.util.List;

import de.uni_muenster.cs.sev.lethal.script.exceptions.ScriptRuntimeError;

/**
 * Class for ranges of Integer numbers inside min and max bounds (inclusive). 
 * @author Philipp
 *
 */
public class RangeClass extends ScriptClass {
	
	/** Singleton RangeClass class instance */
	public static final RangeClass rangeClass = new RangeClass();

	private RangeClass() {
		super("Range", null, RootClass.newStaticClassEnvironment(), true);
	}

	@Override
	public ScriptObject newInstance(List<ScriptObject> args, MethodObject block) {
		if (args.size() != 2 ||
			!(args.get(0) instanceof IntegerObject) ||
			!(args.get(1) instanceof IntegerObject)) throw new ScriptRuntimeError("Range.new(min,max) expects 2 integer arguments");
		
		ScriptObject obj = new RangeObject(((IntegerObject)args.get(0)).getValue() ,((IntegerObject)args.get(1)).getValue());
		return obj;
	}

}


/**
 * Class for ranges of Integer numbers inside min and max bounds (inclusive). 
 * @author Philipp
 *
 */
class RangeObject extends ScriptObject{
	
	private int min;
	private int max;
	
	/**
	 * Creates a new array instance. Only to be called by ArrayClass.newInstance
	 * @param min the lower bound of the Range (inclusive)
	 * @param max the upper bound of the Range (inclusive!)
	 */
	public RangeObject(final int min, final int max) {
		super(RangeClass.rangeClass);
		this.min = min;
		this.max = max;
		this.setMember("min", this.setMember("left", ScriptObject.make(min)));
		this.setMember("max", this.setMember("right", ScriptObject.make(max)));
		
		this.setMember("each", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block){
				if (block == null) throw new ScriptRuntimeError("Array.each needs a block. e.g .each(){|item| ... }");
				List<ScriptObject> blockArgs = new ArrayList<ScriptObject>(1);
				blockArgs.add(null); //dummy for set() to work.
				ScriptObject ret = ScriptObject.nullValue;
				for (int i = min; i <= max; i++){
					blockArgs.set(0, ScriptObject.make(i));
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
				for (int i = max; i >= min; i--){
					blockArgs.set(0, ScriptObject.make(i));
					ret = block.call(blockArgs,null);
				}
				return ret;
			}
		});
		this.setMember("to_a", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block){
				List<ScriptObject> ret = new ArrayList<ScriptObject>(max - min +1);
				for (int i = min; i <= max; i++){
					ret.add(ScriptObject.make(i));
				}
				return new ArrayObject(ret);
			}
		});
	}
	
	@Override
	public String toString(){
		return "(" + min + ".." + max + ")";
	}
	
	@Override
	public boolean equals(Object o){
		if (!(o instanceof RangeObject)) return false;
		return ((RangeObject)o).min == this.min && ((RangeObject)o).max == this.max;
	}
}
