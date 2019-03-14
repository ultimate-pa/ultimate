/*******************************************************************************
 * Copyright (c) 2018 Fraunhofer IEM, Paderborn, Germany.
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * http://www.eclipse.org/legal/epl-2.0.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 * Contributors:
 *     Johannes Spaeth - initial API and implementation
 *******************************************************************************/
package test;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import pathexpression.IRegEx;
import pathexpression.PathExpressionComputer;
import pathexpression.RegEx;


public class PathExpressionTest {
   @Test
   public void simple() {
   IntGraph g = new IntGraph();
   g.addEdge(1, "w", 2);
   PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<Integer, String>(g);
   IRegEx<String> expressionBetween = expr.getExpressionBetween(1, 2);
   IRegEx<String> expected = new RegEx.Plain<String>("w");
   assertEquals(expected, expressionBetween);
   }

   @Test
   public void simple2() {
   IntGraph g = new IntGraph();
   g.addEdge(1, "w", 2);
   g.addEdge(2, "w", 3);
   PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<Integer, String>(g);
   IRegEx<String> expressionBetween = expr.getExpressionBetween(1, 3);
   IRegEx<String> expected = a("w", "w");
   assertEquals(expected, expressionBetween);
   }

   @Test
   public void simple3() {
   IntGraph g = new IntGraph();
   g.addEdge(1, "a", 2);
   g.addEdge(2, "b", 3);
   g.addEdge(3, "c", 4);
   PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<Integer, String>(g);
   IRegEx<String> expressionBetween = expr.getExpressionBetween(1, 4);
   IRegEx<String> expected = a(a("a", "b"), "c");
   assertEquals(expected, expressionBetween);
   }

   @Test
   public void star2() {
   IntGraph g = new IntGraph();
   g.addEdge(1, "a", 2);
   g.addEdge(2, "b", 1);
   PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<Integer, String>(g);
   IRegEx<String> expressionBetween = expr.getExpressionBetween(1, 2);
   IRegEx<String> expected = a("a", star(a("b", "a")));
   assertEquals(expected, expressionBetween);
   }

   @Test
   public void star3() {
   IntGraph g = new IntGraph();
   g.addEdge(1, "a", 2);
   g.addEdge(2, "b", 1);
   g.addEdge(1, "c", 2);
   PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<Integer, String>(g);
   IRegEx<String> expressionBetween = expr.getExpressionBetween(1, 2);
   IRegEx<String> expected = a(u("a", "c"), star(a("b", u("a", "c"))));
   assertEquals(expected, expressionBetween);
   }

   @Test
   public void simple4() {
   IntGraph g = new IntGraph();
   g.addEdge(1, "a", 2);
   g.addEdge(2, "b", 3);
   g.addEdge(3, "c", 4);
   g.addEdge(1, "c", 4);
   PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<Integer, String>(g);
   IRegEx<String> expressionBetween = expr.getExpressionBetween(1, 4);
   IRegEx<String> expected = u("c", a(a("a", "b"), "c"));
   assertEquals(expected, expressionBetween);
   }

   @Test
   public void star() {
   IntGraph g = new IntGraph();
   g.addEdge(1, "a", 2);
   g.addEdge(2, "b", 2);
   g.addEdge(2, "c", 3);
   PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<Integer, String>(g);
   IRegEx<String> expressionBetween = expr.getExpressionBetween(1, 3);
   IRegEx<String> expected = a(a("a", star("b")), "c");
   assertEquals(expected, expressionBetween);
   }

   @Test
   public void union() {
   IntGraph g = new IntGraph();
   g.addEdge(1, "a", 2);
   g.addEdge(2, "b", 3);
   g.addEdge(1, "c", 4);
   g.addEdge(4, "d", 3);
   PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<Integer, String>(g);
   IRegEx<String> expressionBetween = expr.getExpressionBetween(1, 3);
   IRegEx<String> expected = u(a("a", "b"), a("c", "d"));
   assertEquals(expected, expressionBetween);
   }

   @Test
   public void empty() {
   IntGraph g = new IntGraph();
   g.addEdge(2, "a", 1);
   g.addEdge(2, "b", 3);
   g.addEdge(3, "c", 1);
   PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<Integer, String>(g);
   IRegEx<String> expressionBetween = expr.getExpressionBetween(1, 3);
   IRegEx<String> expected = new RegEx.EmptySet<String>();
   assertEquals(expected, expressionBetween);
   }

   @Test
   public void unionAndConcatenate() {
   IntGraph g = new IntGraph();
   g.addEdge(1, "a", 2);
   g.addEdge(2, "b", 4);
   g.addEdge(1, "a", 3);
   g.addEdge(3, "b", 4);
   g.addEdge(4, "c", 5);
   PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<Integer, String>(g);
   IRegEx<String> expressionBetween = expr.getExpressionBetween(1, 5);
   IRegEx<String> expected = a(a("a", "b"), "c");
   assertEquals(expected, expressionBetween);
   }

   @Test
   public void empty2() {
   IntGraph g = new IntGraph();
   g.addEdge(3, "c", 1);
   PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<Integer, String>(g);
   IRegEx<String> expressionBetween = expr.getExpressionBetween(1, 3);
   IRegEx<String> expected = new RegEx.EmptySet<String>();
   assertEquals(expected, expressionBetween);
   }

   @Test
   public void branchWithEps() {
   IntGraph g = new IntGraph();
   g.addEdge(1, "a", 2);
   g.addEdge(2, "v", 4);
   g.addEdge(1, "c", 3);
   g.addEdge(1, "c", 4);
   PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<Integer, String>(g);
   IRegEx<String> expressionBetween = expr.getExpressionBetween(1, 4);
   IRegEx<String> expected = u("c", a("a", "v"));
   assertEquals(expected, expressionBetween);
   }

  @Test
  public void branchWithEps2() {
    IntGraph g = new IntGraph();
    g.addEdge(1, "a", 2);
    g.addEdge(2, "v", 4);
    g.addEdge(1, "c", 3);
    g.addEdge(1, "c", 4);
    PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<Integer, String>(g);
    IRegEx<String> expressionBetween = expr.getExpressionBetween(1, 4);
    IRegEx<String> expected = u("c", a("a", "v"));
    assertEquals(expected, expressionBetween);
  }

  @Test
  public void branchWithEps3() {
    IntGraph g = new IntGraph();
    g.addEdge(1, "a", 2);
    g.addEdge(2, "v", 3);
    g.addEdge(1, "c", 3);
    PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<Integer, String>(g);
    IRegEx<String> expressionBetween = expr.getExpressionBetween(1, 3);
    IRegEx<String> expected = u("c", a("a", "v"));
    assertEquals(expected, expressionBetween);
  }

  @Test
  public void simpleReverse() {
    IntGraph g = new IntGraph();
    g.addEdge(3, "a", 2);
    g.addEdge(2, "v", 1);
    PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<Integer, String>(g);
    IRegEx<String> expressionBetween = expr.getExpressionBetween(3, 1);
    IRegEx<String> expected = a("a", "v");
    assertEquals(expected, expressionBetween);
  }

  @Test
  public void loop() {
    IntGraph g = new IntGraph();
    g.addEdge(1, "12", 2);
    g.addEdge(2, "23", 3);
    g.addEdge(3, "34", 4);
    g.addEdge(4, "43", 3);
    PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<Integer, String>(g);
    IRegEx<String> expressionBetween = expr.getExpressionBetween(1, 3);
    IRegEx<String> expected = u(a("12", "23"),a(a(a(a("12","23"),"34"), star(a("43","34"))),"43"));
    assertEquals(expected, expressionBetween);
  }


  @Test
  public void loop2() {
    IntGraph g = new IntGraph();
    g.addEdge(1, "12", 2);
    g.addEdge(2,"21",1);
    g.addEdge(2, "23", 3);
    g.addEdge(3, "34", 4);
    g.addEdge(4, "43", 3);
    PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<Integer, String>(g);
    IRegEx<String> expressionBetween = expr.getExpressionBetween(1, 3);
    IRegEx<String> expected = u(a(a("12", star(a("21", "12"))), "23"), a(a(a(a(a("12", star(a("21", "12"))), "23"), "34"), star(a("43", "34"))), "43"));
    assertEquals(expected, expressionBetween);
  }

  @Test
  public void loop3() {
    IntGraph g = new IntGraph();
    g.addEdge(1, "12", 2);
    g.addEdge(2, "23", 3);
    g.addEdge(3, "32", 2);
    g.addEdge(3, "34", 4);
    g.addEdge(4, "41", 1);
    PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<Integer, String>(g);
    IRegEx<String> expressionBetween = expr.getExpressionBetween(1, 1);
    IRegEx<String> expected = a(a(a(a(a("12", "23"), star(a("32", "23"))), "34"), star(a(a(a(a("41", "12"), "23"), star(a("32", "23"))), "34"))), "41");
    assertEquals(expected, expressionBetween);
  }

  @Test
  public void loop4() {
    IntGraph g = new IntGraph();
    g.addEdge(1, "13", 3);
    g.addEdge(3, "31", 1);
    g.addEdge(3, "34", 4);
    g.addEdge(4, "41", 1);
    PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<Integer, String>(g);
    IRegEx<String> expressionBetween = expr.getExpressionBetween(1, 1);
    IRegEx<String> expected = u(a(a(a(a("13", star(a("31", "13"))), "34"), star(a(a(a("41", "13"), star(a("31", "13"))), "34"))), "41"), a(u(a("13", star(a("31", "13"))), a(a(a(a("13", star(a("31", "13"))), "34"), star(a(a(a("41", "13"), star(a("31", "13"))), "34"))), a(a("41", "13"), star(a("31", "13"))))), "31"));
    assertEquals(expected, expressionBetween);
  }

  private static IRegEx<String> e(String e) {
    return new RegEx.Plain<String>(e);
  }


  private static IRegEx<String> a(IRegEx<String> a, IRegEx<String> b) {
    return RegEx.<String>concatenate(a, b);
  }

  private static IRegEx<String> a(String a, IRegEx<String> b) {
    return a(e(a), b);
  }

  private static IRegEx<String> a(IRegEx<String> a, String b) {
    return a(a, e(b));
  }

  private static IRegEx<String> a(String a, String b) {
    return a(e(a), e(b));
  }

  private static IRegEx<String> u(IRegEx<String> a, IRegEx<String> b) {
    return RegEx.<String>union(a, b);
  }

  private static IRegEx<String> u(String a, String b) {
    return u(e(a), e(b));
  }

  private static IRegEx<String> u(IRegEx<String> a, String b) {
    return u(a, e(b));
  }

  private static IRegEx<String> u(String a, IRegEx<String> b) {
    return u(e(a), b);
  }

  private static IRegEx<String> star(IRegEx<String> a) {
    return RegEx.<String>star(a);
  }

  private static IRegEx<String> star(String a) {
    return star(e(a));
  }

  private static String toTestString(IRegEx<String> regEx){
     if(regEx instanceof RegEx.EmptySet){
       return "";
     } else if(regEx instanceof RegEx.Plain){
       return String.format("\"%s\"",((RegEx.Plain) regEx).v);
     } else if(regEx instanceof RegEx.Concatenate){
       RegEx.Concatenate concat = (RegEx.Concatenate) regEx;
       return String.format("a(%s, %s)",toTestString(concat.a), toTestString(concat.b));
     } else if(regEx instanceof RegEx.Union){
       RegEx.Union union = (RegEx.Union) regEx;
       return String.format("u(%s, %s)", toTestString(union.a), toTestString(union.b));
     } else if(regEx instanceof RegEx.Star){
       return String.format("star(%s)", toTestString(((RegEx.Star) regEx).a));
     } else{
       throw new IllegalArgumentException("Unhandled regex: " + regEx);
     }
  }

}
