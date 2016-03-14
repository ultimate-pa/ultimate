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
package de.uni_muenster.cs.sev.lethal.parser.xml;


import java.io.*;
import java.util.*;

import javax.xml.parsers.*;

import org.xml.sax.*;
import org.xml.sax.helpers.*;

import de.uni_muenster.cs.sev.lethal.symbol.common.*;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.tree.special.StringTree;
import de.uni_muenster.cs.sev.lethal.factories.NamedSymbolTreeFactory;
import de.uni_muenster.cs.sev.lethal.factories.TreeFactory;

/**
 * Parser for creating trees and Hedges from XML files
 * @author Philipp
 *
 */
public class XMLTreeParser {

	/**
	 * Parse a ranked tree from an XML Document.
	 * @param xmlfile XML File to read.
	 * @return the parsed tree.
	 * @throws ParserConfigurationException XML Parser exception
	 * @throws SAXException XML Parser exception
	 * @throws IOException File read error.
	 */
	public static Tree<RankedSymbol> parseTreeFromXML(File xmlfile) throws ParserConfigurationException, SAXException, IOException{
		return XMLTreeParser.parseFromXML(xmlfile, false, RankedSymbol.class);
	}
	
	/**
	 * Parse a ranked tree from an XML Document.
	 * @param xmlfile XML File to read.
	 * @param includeAttributes if true attributes of XML Elements will be included in the resulting tree, otherwise they will be ignored.
	 * @return the parsed tree.
	 * @throws ParserConfigurationException XML Parser exception
	 * @throws SAXException XML Parser exception
	 * @throws IOException File read error.
	 */
	public static Tree<RankedSymbol> parseTreeFromXML(File xmlfile, boolean includeAttributes) throws ParserConfigurationException, SAXException, IOException{
		return XMLTreeParser.parseFromXML(xmlfile, includeAttributes, RankedSymbol.class);
	}
	
	/**
	 * Parse an unranked tree (hedge) from an XML Document.
	 * @param xmlfile XML File to read.
	 * @return the parsed tree.
	 * @throws ParserConfigurationException XML Parser exception
	 * @throws SAXException XML Parser exception
	 * @throws IOException File read error.
	 */
	public static Tree<UnrankedSymbol> parseHedgeFromXML(File xmlfile) throws ParserConfigurationException, SAXException, IOException{
		return XMLTreeParser.parseFromXML(xmlfile, false, UnrankedSymbol.class);
	}
	
	/**
	 * Parse an unranked tree (hedge) from an XML Document.
	 * @param xmlfile XML File to read.
	 * @param includeAttributes if true attributes of XML Elements will be included in the resulting hedge, otherwise they will be ignored. 
	 * @return the parsed tree.
	 * @throws ParserConfigurationException XML Parser exception
	 * @throws SAXException XML Parser exception
	 * @throws IOException File read error.
	 */
	public static Tree<UnrankedSymbol> parseHedgeFromXML(File xmlfile, boolean includeAttributes) throws ParserConfigurationException, SAXException, IOException{
		return XMLTreeParser.parseFromXML(xmlfile, includeAttributes, UnrankedSymbol.class);
	}
	
	/**
	 * Parse a tree from an XML Document.
	 * @param xmlfile XML File to read.
	 * @param symClass class of the symbols in the resulting tree.
	 * @param includeAttributes if true attributes of XML Elements will be included in the resulting tree, otherwise they will be ignored.
	 * @param <S> class of the symbols in the resulting tree.
	 * @return the parsed tree.
	 * @throws ParserConfigurationException XML Parser exception
	 * @throws SAXException XML Parser exception
	 * @throws IOException File read error.
	 */
	public static <S extends Symbol> Tree<S> parseFromXML(File xmlfile, boolean includeAttributes, Class<S> symClass) throws ParserConfigurationException, SAXException, IOException{
		NamedSymbolTreeFactory<S> tc = TreeFactory.getTreeFactory(symClass);
		SAXParser parser = SAXParserFactory.newInstance().newSAXParser();
		SAXParserHandler<S> handler = new SAXParserHandler<S>(tc, includeAttributes);
		parser.parse(xmlfile, handler);
		return handler.getResultTree();
	}
	
}

class SAXParserHandler<S extends Symbol> extends DefaultHandler{
	
	private Stack<XMLNode> nodes = new Stack<XMLNode>();
	private NamedSymbolTreeFactory<S> tc;
	private boolean includeAttributes;
	private Tree<S> resultTree;
	
	public SAXParserHandler(NamedSymbolTreeFactory<S> tc, boolean includeAttributes){
		this.tc = tc;
		this.includeAttributes = includeAttributes;
	}
	
	public Tree<S> getResultTree(){
		return this.resultTree;
	}


	@Override
	public void startElement(String uri, String localName, String qName, Attributes attributes) throws SAXException {
		XMLNode node = new XMLNode(qName);
		if (includeAttributes && attributes.getLength() != 0){
			List<Tree<S>> attrs = new ArrayList<Tree<S>>();
			for (int i = 0; i < attributes.getLength(); i++){
				List<Tree<S>> subtrees = new ArrayList<Tree<S>>(1);
				subtrees.add(new StringTree<S>(tc.getSymbolClass(), attributes.getValue(i)));
				attrs.add(tc.makeTreeFromName(attributes.getLocalName(i),subtrees));
			}
			node.addSubtree(tc.makeTreeFromName("_attr_", attrs));
		}
		nodes.push(node);
	}
	
	
	
	@Override
	public void characters(char[] ch, int start, int length) throws SAXException {
		nodes.peek().addContent(ch, start, length);
	}

	@Override
	public void endElement(String uri, String localName, String qName) throws SAXException {
		XMLNode topNode = nodes.pop();
		
		if (this.nodes.empty()){
			this.resultTree = topNode.makeTree(); //stack is empty this was the last element, thus the tree is complete, we are done.
		} else {
			nodes.peek().addSubtree(topNode.makeTree()); //add this tree as a subtree of the next element of the stack (parent of this tree)
		}
	}

	class XMLNode{
		public String name;
		public StringBuffer content = new StringBuffer();
		public List<Tree<S>> subtrees = new ArrayList<Tree<S>>();
		
		public XMLNode(String name){
			this.name = name;
		}
		
		public void addSubtree(Tree<S> subtree){
			this.subtrees.add(subtree);
		}
		public void addContent(char[] str, int offset, int len){
			this.content.append(str, offset, len);
		}
		
		public Tree<S> makeTree(){
			String scontent = this.content.toString().trim();
			if (scontent.length() == 0) scontent = null;
			return SAXParserHandler.this.tc.makeTreeFromName(this.name, this.subtrees);
		}
	}
	
}
