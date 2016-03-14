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
/**
 * 
 */
package de.uni_muenster.cs.sev.lethal.hom;

import java.util.Collection;

import de.uni_muenster.cs.sev.lethal.symbol.common.BiSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.Variable;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;

/**
 * Represents a tree homomorphism as a mapping from function symbols to variable trees. 
 * This is adequate since such a mapping characterizes a tree homomorphism completely. <br>
 * A homomorphism on {@link Tree trees} h: {Trees over alphabet F} -> {Trees over alphabet G} is given 
 * by a function hom : F -> {variable trees containing variables and symbols of the alphabet G}, 
 * where each symbol f of arity n is dedicated to a tree with symbols of G and at most n 
 * variables x_0,...,x_{n-1}. <br>
 * For a tree t=f(t_0,...,t_{n-1}), hom(t) is given by replacing the each variable x_i by hom(t_i) in h(f).
 * 
 * Possible methods: consider {@link HomOps}.
 * 
 * @author Dorothea, Irene, Martin
 *
 * @param <F> type of function symbols in source alphabet of the homomorphism
 * @param <G> type of function symbols occurring in images of the homomorphism
 * @param <V> type of homomorphism variables occurring in images of the homomorphism
 */
public interface Hom<F extends RankedSymbol, G extends RankedSymbol, V extends Variable> {
	
    /**
     * Returns whether a specified symbol is contained in the source alphabet of the homomorphism.
     * 
     * @param symbol symbol to be checked
     * @return true if symbol is contained in source alphabet, false otherwise
     */
    boolean containsSrcSymbol(F symbol);
    
    
    /**
     * Getter for the source alphabet of the homomorphism.
     * 
     * @return the source alphabet of the homomorphism
     */
    Collection<F> getSrcAlphabet();
    
    
    /**
     * Returns the variable tree to which the given symbol is mapped by the homomorphism.
     * 
     * @param f function symbol of which the homomorphism image is to be retrieved
     * @return the variable tree to which f is mapped by the homomorphism
     */
    Tree<? extends BiSymbol<G,V>> imageOf(F f);
    
}
