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

import de.uni_muenster.cs.sev.lethal.hom.EasyHom;

import java.util.List;

import de.uni_muenster.cs.sev.lethal.parser.homomorphism.HomomorphismParser;
import de.uni_muenster.cs.sev.lethal.script.exceptions.ScriptRuntimeError;

/**
 * Encapsulates a tree homomorphism (@see hom.Hom) for use in the scripting language.
 * @author Philipp
 *
 */
public class HomomorphismClass extends ScriptClass {
	
	/** Singleton HomomorphismClass class instance */
	public static final HomomorphismClass homClass = new HomomorphismClass();
	
	private HomomorphismClass() {
		super("Homomorphism", null, RootClass.newStaticClassEnvironment(), true);
	}

	@Override
	public ScriptObject newInstance(List<ScriptObject> args, MethodObject block) {
		StringBuilder rulesString = new StringBuilder();
		for (ScriptObject arg : args){
			if (!(arg instanceof StringObject)) throw new ScriptRuntimeError("Homomorphism.new exptects a String parameter");
			rulesString.append(((StringObject)arg).getValue());
			rulesString.append('\n');
		}
		try {
			return new HomomorphismObject(HomomorphismParser.parseString(rulesString.toString()));
		} catch (Exception e) {
			throw new ScriptRuntimeError("Homomorphism Parser Exception:" + e.getMessage());
		}
	}

}

class HomomorphismObject extends ScriptObject {
	
	private EasyHom homomorphism;
	
	public HomomorphismObject(EasyHom homomorphism) {
		super(HomomorphismClass.homClass);
		this.homomorphism = homomorphism;
		
		this.getEnvironment().bindLocal("linear", new Method(0) {
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				return ScriptObject.make(HomomorphismObject.this.homomorphism.isLinear());
			}
		});
		this.getEnvironment().bindLocal("apply", new Method(1) {
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {

				ScriptObject arg = args.get(0);	
				if (arg instanceof TreeObject){
					TreeObject to = (TreeObject)arg;
					return new TreeObject(HomomorphismObject.this.homomorphism.apply(to.getTree()));
				} else if (arg instanceof FTAObject){
					FTAObject ftao = (FTAObject)arg;
					return new FTAObject(HomomorphismObject.this.homomorphism.applyOnAutomaton(ftao.getAutomaton()));
				} else {
					throw new ScriptRuntimeError("Homomorphism.apply expects Tree or FTA as parameter");
				}
			}
		});

		this.getEnvironment().bindLocal("apply_inverse", new Method(1) {
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				ScriptObject arg = args.get(0);	
				if (arg instanceof FTAObject){
					FTAObject ftao = (FTAObject)arg;
					return new FTAObject(HomomorphismObject.this.homomorphism.applyInverseOnAutomaton(ftao.getAutomaton()));
				} else {
					throw new ScriptRuntimeError("Homomorphism.apply_inverse expects FTA as parameter");
				}
			}
		});
		
	}
}
