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
package de.uni_muenster.cs.sev.lethal.gui;

import java.awt.Color;
import java.awt.Graphics;
import java.awt.Point;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.geom.Point2D;
import java.awt.geom.Rectangle2D;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.List;

import javax.swing.JComponent;

import de.uni_muenster.cs.sev.lethal.factories.NamedSymbolTreeFactory;
import de.uni_muenster.cs.sev.lethal.factories.TreeFactory;
import de.uni_muenster.cs.sev.lethal.symbol.common.Symbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;

/**
 * 
 */
public class TreeBreak extends TreeViewer {
	
	private NamedSymbolTreeFactory<Symbol> tf;
	
	private Thread gameThread;
	private boolean running = false;
	private boolean abort = false;
	
	private static final int WIDTH = 600;
	private static final int HEIGHT = 400;
	private static final int BASELINE = 360;
	private static final int BALL_RADIUS = 5;
	private static final int PADDLE_WIDTH = 60;
	private static final int PADDLE_HEIGHT = 4;
	
	private static final Color paddleColor = new Color(120,60,0);
	
	private Point2D.Float ballPos = new Point2D.Float(); //Center of the ball
	private Point2D.Float newBallPos = new Point2D.Float(); //Center of the ball
	private Point2D.Float ballVelocity = new Point2D.Float();
	private Point paddlePos = new Point(WIDTH / 2, BASELINE); //Center of the upper edge of the paddle
	private Point mousePoint = new Point(paddlePos);
	private int lives;
	
	private Calendar cal = Calendar.getInstance();
	
	/**
	 * Constructor 
	 * @param <S> Symbol type used in the tree factory
	 * @param tf tree factory used to create to create new trees.
	 */
	@SuppressWarnings("unchecked")
	public <S extends Symbol> TreeBreak(final NamedSymbolTreeFactory<S> tf) {
		super(tf.generateRandomTree(7, 17, 17));
		this.tf = (NamedSymbolTreeFactory<Symbol>)tf;
		this.toolbar.setEnabled(false);
		gameThread = new Thread(){
			@Override
			public void run() {
				System.out.println("Game Thread started");
				while (!abort && lives > 0){
					long tStart = cal.getTimeInMillis();
					nextStep();
					try{
						int frameTime = (int)(cal.getTimeInMillis() - tStart);
						//if (running) System.out.println("Frame Time: " + frameTime + "ms");
						if (frameTime < 5) Thread.sleep(5 - frameTime);
					} catch (InterruptedException e) { /*don't care */}
				}
				System.out.println("Game Thread exited");
			}
		};
		this.paintBox.addMouseMotionListener(new MouseAdapter(){
			@Override
			public void mouseMoved(MouseEvent e) {
				mousePoint = e.getPoint();
			}
		});
		this.paintBox.addMouseListener(new MouseAdapter(){
			@Override
			public void mousePressed(MouseEvent e) {
				if (getTree() == null) {setTree(tf.generateRandomTree(7, 17, 17)); init(3);}
				if (e.getButton() == MouseEvent.BUTTON1) running = !running;
			}
			
		});
		
		init(3);
		gameThread.start();
	}

	private void init(int lives){
		this.lives = lives;
		this.ballPos.x = WIDTH / 2;
		this.ballPos.y =  BASELINE - BALL_RADIUS;
		this.ballVelocity.x = 0.7F;
		this.ballVelocity.y = -0.7F;
		this.running = false;
	}
	
	private void nextStep(){
		Graphics g = this.paintBox.getGraphics();
		if (g == null) return;
		String s = "Lives: " + lives;
		
		Rectangle2D srect = g.getFontMetrics().getStringBounds(s, g);
		g.setColor(Color.WHITE);
		g.fillRect(5, 5, (int)srect.getWidth(), (int)srect.getHeight());

		g.setColor(Color.BLACK);
		g.drawRect(0, 0, WIDTH, HEIGHT);
		g.drawString(s, 5, g.getFontMetrics().getHeight());
		
		//if (paddlePos.x != mousePoint.x){
			g.setColor(Color.WHITE);
			g.fillRect(paddlePos.x - PADDLE_WIDTH / 2, paddlePos.y, PADDLE_WIDTH+1, PADDLE_HEIGHT+1);
			
			paddlePos.x = mousePoint.x;
			
			g.setColor(paddleColor);
			g.fillRect(paddlePos.x - PADDLE_WIDTH / 2, paddlePos.y, PADDLE_WIDTH, PADDLE_HEIGHT);
			g.setColor(Color.BLACK);
			g.drawRect(paddlePos.x - PADDLE_WIDTH / 2, paddlePos.y, PADDLE_WIDTH, PADDLE_HEIGHT);
		//}
		
		if (running){
		
			if (nodeInfos == null) calcNodeInfos(g,this.tree);
			
			//Preliminary calculation before collision checks
			newBallPos.x = (ballPos.x + ballVelocity.x);
			newBallPos.y = (ballPos.y + ballVelocity.y);
			
			//outer bounds hit
			if ((newBallPos.x + BALL_RADIUS > WIDTH) || (newBallPos.x < BALL_RADIUS)) ballVelocity.x = -ballVelocity.x; 
			if (newBallPos.y < BALL_RADIUS) ballVelocity.y = -ballVelocity.y;
			
			//node hit
			for (NodeInfo node : this.nodeInfos){
				if (node.rect.contains(newBallPos.x, newBallPos.y - BALL_RADIUS)){ //upper edge hit
					removeNode(node);
					ballVelocity.y = -ballVelocity.y;
					break;
				}
				if (node.rect.contains(newBallPos.x, newBallPos.y + BALL_RADIUS)){ //lower edge hit
					removeNode(node);
					ballVelocity.y = -ballVelocity.y;
					break;
				}
				if (node.rect.contains(newBallPos.x - BALL_RADIUS, newBallPos.y)){ //left edge hit
					removeNode(node);
					ballVelocity.x = -ballVelocity.x;
					break;
				}
				if (node.rect.contains(newBallPos.x + BALL_RADIUS, newBallPos.y)){ //right edge hit
					removeNode(node);
					ballVelocity.x = -ballVelocity.x;
					break;
				}
			}
			
			//paddle hit
			if (newBallPos.y + BALL_RADIUS > paddlePos.y && ballPos.y + BALL_RADIUS <= paddlePos.y){
				if ((newBallPos.x + BALL_RADIUS >= paddlePos.x - (PADDLE_WIDTH / 2)) && (newBallPos.x - BALL_RADIUS <= paddlePos.x + (PADDLE_WIDTH / 2))){
					ballVelocity.x = 0.1F + (1.5F * (newBallPos.x - paddlePos.x) / (PADDLE_WIDTH / 2));
					ballVelocity.y = -ballVelocity.y; 
				}
			}
			
			//loss
			if (newBallPos.y + BALL_RADIUS > HEIGHT){
				init(lives - 1);
				if (lives == 0) g.drawString("Game Over", 5, g.getFontMetrics().getHeight());
			}
			
			g.setColor(Color.WHITE);
			g.fillOval((int)ballPos.x- BALL_RADIUS, (int)ballPos.y - BALL_RADIUS, BALL_RADIUS * 2, BALL_RADIUS * 2);
			ballPos.x += ballVelocity.x;
			ballPos.y += ballVelocity.y;
		}
		g.setColor(paddleColor);
		g.fillOval((int)ballPos.x - BALL_RADIUS, (int)ballPos.y - BALL_RADIUS, BALL_RADIUS * 2, BALL_RADIUS * 2);
		
	}
	@Override
	public void paintTree(JComponent comp, Graphics g) {
		synchronized(this){
			super.paintTree(comp,g);
			g.setColor(paddleColor);
			g.fillRect(paddlePos.x - PADDLE_WIDTH / 2, paddlePos.y, PADDLE_WIDTH, PADDLE_HEIGHT);
			g.setColor(Color.BLACK);
			g.drawRect(paddlePos.x - PADDLE_WIDTH / 2, paddlePos.y, PADDLE_WIDTH, PADDLE_HEIGHT);
			g.setColor(Color.BLACK);
			g.drawRect(0, 0, WIDTH, HEIGHT);
		}
	}
	
	@SuppressWarnings("unchecked")
	private <S extends Symbol> void removeNode(NodeInfo node){
		synchronized(this){
			NodeInfo parent = node.parent;
			if (parent == null){
				this.setTree(null);
				win();
				return;
			}
			List<Tree<Symbol>> subtrees = new ArrayList<Tree<Symbol>>(parent.tree.getSubTrees().size() - 1);
			for (int i = 0; i < parent.tree.getSubTrees().size(); i++){
				if (i != node.childIndex) subtrees.add((Tree<Symbol>) parent.tree.getSubTrees().get(i));
			}
			
			Tree<Symbol> tree = tf.makeTreeFromName(node.parent.tree.getSymbol().toString(), subtrees);
			node = parent;
			parent = parent.parent;
			while (parent != null){
				subtrees = new ArrayList<Tree<Symbol>>(parent.tree.getSubTrees().size() - 1);
				for (int i = 0; i < parent.tree.getSubTrees().size(); i++){
					if (i != node.childIndex){
						subtrees.add((Tree<Symbol>) parent.tree.getSubTrees().get(i));
					} else {
						subtrees.add(tree);
					}
				}
				
				tree = TreeFactory.getTreeFactory().<Symbol>makeTreeFromSymbol(node.parent.tree.getSymbol(), subtrees);
				node = parent;
				parent = parent.parent;
			}
			this.setTree(tree);
			if (nodeInfos == null) calcNodeInfos(paintBox.getGraphics(),this.tree);
		}
	}
	
	
	private void win(){
		running = false;
	}
	
	@Override
	public void setVisible(boolean visible){
		super.setVisible(visible);
		if (!visible) abort = true;
	}
	
}
