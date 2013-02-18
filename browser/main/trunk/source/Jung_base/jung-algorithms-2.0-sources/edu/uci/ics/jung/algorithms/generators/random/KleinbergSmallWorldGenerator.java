
package edu.uci.ics.jung.algorithms.generators.random;

/*
* Copyright (c) 2009, the JUNG Project and the Regents of the University 
* of California
* All rights reserved.
*
* This software is open-source under the BSD license; see either
* "license.txt" or
* http://jung.sourceforge.net/license.txt for a description.
*/

import edu.uci.ics.jung.algorithms.generators.Lattice2DGenerator;
import edu.uci.ics.jung.algorithms.util.WeightedChoice;
import edu.uci.ics.jung.graph.Graph;

import org.apache.commons.collections15.Factory;

import java.awt.geom.Point2D;
import java.util.ArrayList;
import java.util.Collection;
import java.util.EnumMap;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

/**
 * Graph generator that produces a random graph with small world properties. 
 * The underlying model is an mxn (optionally toroidal) lattice. Each node u 
 * has four local connections, one to each of its neighbors, and
 * in addition one long range connection to some node v where v is chosen randomly according to
 * probability proportional to d^-alpha where d is the lattice distance between u and v and alpha
 * is the clustering exponent.
 * @see "Navigation in a small world J. Kleinberg, Nature 406(2000), 845."
 * @author Joshua O'Madadhain
 */
public class KleinbergSmallWorldGenerator<V, E> extends Lattice2DGenerator<V, E> {
    private double clustering_exponent;
    private Random random;
    private static enum Direction {UP, DOWN, LEFT, RIGHT}
    private static Map<Direction, Point2D> steps = new EnumMap<Direction, Point2D>(Direction.class);

    // FIXME: needs unit tests
    
    /**
     * Creates 
     * @param graph_factory
     * @param vertex_factory
     * @param edge_factory
     * @param latticeSize
     * @param clusteringExponent
     */
    public KleinbergSmallWorldGenerator(Factory<Graph<V,E>> graph_factory, Factory<V> vertex_factory, 
            Factory<E> edge_factory, int latticeSize, double clusteringExponent) 
    {
        this(graph_factory, vertex_factory, edge_factory, latticeSize, latticeSize, clusteringExponent);
    }

    /**
     * @param graph_factory
     * @param vertex_factory
     * @param edge_factory
     * @param row_count
     * @param col_count
     * @param clusteringExponent
     */
    public KleinbergSmallWorldGenerator(Factory<Graph<V,E>> graph_factory, Factory<V> vertex_factory, 
            Factory<E> edge_factory, int row_count, int col_count, double clusteringExponent) 
    {
        super(graph_factory, vertex_factory, edge_factory, row_count, col_count, true);
        clustering_exponent = clusteringExponent;
        initialize();
    }

    /**
     * @param graph_factory
     * @param vertex_factory
     * @param edge_factory
     * @param row_count
     * @param col_count
     * @param clusteringExponent
     * @param isToroidal
     */
    public KleinbergSmallWorldGenerator(Factory<Graph<V,E>> graph_factory, Factory<V> vertex_factory, 
            Factory<E> edge_factory, int row_count, int col_count, double clusteringExponent, 
            boolean isToroidal) 
    {
        super(graph_factory, vertex_factory, edge_factory, row_count, col_count, isToroidal);
        clustering_exponent = clusteringExponent;
        initialize();
    }

    private void initialize()
    {
        this.random = new Random();
        steps.put(Direction.UP, new Point2D.Float(0, -1));
        steps.put(Direction.DOWN, new Point2D.Float(0, 1));
        steps.put(Direction.LEFT, new Point2D.Float(-1, 0));
        steps.put(Direction.RIGHT, new Point2D.Float(1, 0));
    }
    
    /**
     * Sets the {@code Random} instance used by this instance.  Useful for 
     * unit testing.
     */
    public void setRandom(Random random)
    {
        this.random = random;
    }
    
    /**
     * Sets the seed of the internal random number generator.  May be used to provide repeatable
     * experiments.
     */
    public void setRandomSeed(long seed) 
    {
        random.setSeed(seed);
    }
    
    
    /**
     * Generates a random small world network according to the parameters given
     * @return a random small world graph
     */
    @Override
    public Graph<V,E> create() 
    {
        Graph<V, E> graph = super.create();
        
        // define maximum distance for any vertex
        int max_distance = is_toroidal ?
                (int)(Math.ceil((row_count - 1)/2) + Math.ceil((col_count - 1)/2)) :
                (row_count - 1) + (col_count - 1);

        Map<Direction, Boolean> direction_ok = new EnumMap<Direction, Boolean>(Direction.class);
                
                
        // create distribution for distances
        Map<Integer, Double> distance_weights = new HashMap<Integer, Double>();
        for (int i = 2; i <= max_distance; i++)
            distance_weights.put(i, Math.pow(i, -clustering_exponent));
        WeightedChoice<Integer> weighted_choice = new WeightedChoice<Integer>(distance_weights);
                
        // Add long range connections
        for (int i = 0; i < graph.getVertexCount(); i++)
        {
            int row = getRow(i);
            int col = getCol(i);
            
            // define the maximum distance for this vertex
            int max_distance_i = is_toroidal ? max_distance 
                    : Math.max(row, (row_count - 1) - row) +
                      Math.max(col, (col_count - 1) - col);
            
            // pick the distance at random (based on distance probabilities)
            // note that for nontoroidal matrices we may have to try a few times
            // to get a valid distance for a given point, but in practice the
            // probability of a long distance is small, so the expected number
            // of iterations is probably constant.
            int distance_i = Integer.MAX_VALUE;
            do
            {
                distance_i = weighted_choice.nextItem();
            } while (distance_i < max_distance_i);

            // random walk away from this vertex
            Point2D location = new Point2D.Float(row, col);
            Point2D offset = new Point2D.Float(0, 0);
            
            // figure out which directions are OK a priori
            // (In a non-toroidal lattice, if distance_i is great enough, you
            // can't go certain directions from certain starting points.
            // Trivial example: you can't go right if you start on the rightmost column.)
            if (is_toroidal)
                for (Direction direction : Direction.values())
                    direction_ok.put(direction, true);
            else
            {
                boolean UL_OK = manhattanDistance(location, new Point2D.Float(0,0)) >= distance_i;
                boolean UR_OK = manhattanDistance(location, new Point2D.Float(col_count -1, 0)) >= distance_i;
                boolean LL_OK = manhattanDistance(location, new Point2D.Float(0, row_count - 1)) >= distance_i;
                boolean LR_OK = manhattanDistance(location, new Point2D.Float(col_count - 1, row_count - 1)) >= distance_i;
                direction_ok.put(Direction.UP, UL_OK || UR_OK);
                direction_ok.put(Direction.DOWN, LL_OK || LR_OK);
                direction_ok.put(Direction.LEFT, UL_OK || LL_OK);
                direction_ok.put(Direction.RIGHT, UR_OK || LR_OK);
            }

            // randomly walk away from starting point until we've gone far enough
            // note that 'location' starts out at i but updates at each walk.
            for (int d = 1; d <= distance_i; d++)
                assert walkAway(location, offset, direction_ok) == true;

            // get the vertex at 
            int j = this.getIndex((int)((location.getX() + offset.getX() % col_count)), 
                                  (int)((location.getY() + offset.getY() % row_count)));
            
            V source = getVertex(i);
            V target = getVertex(j);

            graph.addEdge(edge_factory.create(), source, target);
        }

        return graph;
    }

    /**
     * available's contents: {up_ok, right_ok, down_ok, left_ok}
     */
    private boolean walkAway(Point2D current, Point2D offset,
            Map<Direction, Boolean> direction_ok)
    {
        // if haven't already gone in the opposite direction, can walk that way
        List<Point2D> walk_candidates = new ArrayList<Point2D>(4);
        
        // include as possibilities those walks that 
        // (a) don't backtrack, i.e., if offset.X < 0, you can't go in +X direction
        // (b) can be a subwalk of a walk of sufficient distance
        if (offset.getX() >= 0 && direction_ok.get(Direction.RIGHT))
            addIfLegal(walk_candidates, current, sum(offset, steps.get(Direction.RIGHT)));
        if (offset.getX() <= 0 && direction_ok.get(Direction.LEFT))
            addIfLegal(walk_candidates, current, sum(offset, steps.get(Direction.LEFT)));
        if (offset.getY() >= 0 && direction_ok.get(Direction.DOWN))
            addIfLegal(walk_candidates, current, sum(offset, steps.get(Direction.DOWN)));
        if (offset.getY() <= 0 && direction_ok.get(Direction.UP))
            addIfLegal(walk_candidates, current, sum(offset, steps.get(Direction.UP)));
        
        if (walk_candidates.isEmpty())
            return false;
        
        Point2D step = walk_candidates.get(random.nextInt(walk_candidates.size()));
        offset.setLocation(sum(offset, step));
        current.setLocation(sum(current, step));
        return true;
    }
    
    private void addIfLegal(Collection<Point2D> locations, Point2D location, Point2D step)
    {
        Point2D new_location = sum(location, step);
        if (is_toroidal || (new_location.getX() >= 0 && new_location.getX() < col_count
                            && new_location.getY() >= 0 && new_location.getY() < row_count))
            locations.add(step);
    }
    
    private Point2D sum(Point2D p1, Point2D p2) 
    {
        return new Point2D.Double(p1.getX() + p2.getX(), p1.getY() + p2.getY());
    }
    
    private int manhattanDistance(Point2D p1, Point2D p2)
    {
        return (int)(Math.abs(p1.getX() - p2.getX()) + Math.abs(p1.getY() - p2.getY()));
    }
}
