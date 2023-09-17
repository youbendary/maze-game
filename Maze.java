import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Random;

import tester.*;
import javalib.impworld.*;
import java.awt.Color;
import javalib.worldimages.*;

// DOCUMENTATION ON HOW TO NAVIGATE MAZE:
// WITH GIVEN DIMENSIONS, USER CAN CHOOSE TO USED BREADTH OR DEPTH FIRST SEARCH TO SOLVE THE MAZE, 
// HIGHLIGHTING THE CELLS THAT ARE CHECKED IN THE PROCESS.
// THIS DECISION CAN BE MADE BY THE KEY THEY PRESS
// ("b" begins a breadth first search and "d", a depth first search).
// THE USER CAN ALSO PRESS THE KEY "r" TO DISPLAY A NEW RANDOM MAZE 
// WHERE THE USER CAN AGAIN CHOOSE A SEARCH METHOD
// WHEN THE FINAL CELL IS REACHED, THE SOLUTION PATH IS THEN DISLPLAYED, 
// HIGHLIGTING THE CELLS AS IT MOVES BACKWARDS FROM THE FINAL CELL.
// AFTER THE SOLUTION PATH IS DISPLAYED, THE WORLD ENDS.

// to represent the class cell
class Cell {
  Posn id;

  // the four adjacent cells to this one
  Cell left;
  Cell top;
  Cell right;
  Cell bottom;

  // constructor
  Cell(Posn id) {
    this.id = id;
  }

  // determines if two cells are equal
  @Override
  public boolean equals(Object o) {
    Cell cell = (Cell) o;
    return this.id.equals(cell.id);
  }

  // modifies cell's hashCode
  @Override
  public int hashCode() {
    return 31 + this.id.x + this.id.y;
  }

  // EFFECT: sets the cell's top cell to the given cell
  void setTop(Cell top) {
    this.top = top;
  }

  // EFFECT: sets the cell's bottom cell to the given cell
  void setBottom(Cell bottom) {
    this.bottom = bottom;
  }

  // EFFECT: sets the cell's left cell to the given cell
  void setLeft(Cell left) {
    this.left = left;
  }

  // EFFECT: sets the cell's right cell to the given cell
  void setRight(Cell right) {
    this.right = right;
  }

}

//represents edge class 
class Edge {
  int weight;
  Cell node1;
  Cell node2;

  // constructor
  Edge(Cell node1, Cell node2, int weight) {
    this.weight = weight;
    this.node1 = node1;
    this.node2 = node2;
  }

  // returns weight of edge
  int getWeight() {
    return this.weight;
  }

  // returns first node of edge
  Cell getNode1() {
    return this.node1;
  }

  // returnds second node of edge
  Cell getNode2() {
    return this.node2;
  }

  // returns true if both entered nodes are represented in edge
  boolean containsBothNodes(Cell c1, Cell c2) {
    return ((c1.equals(node1) || c1.equals(node2)) && (c2.equals(node1) || c2.equals(node2)));
  }

  // returns the other cell in the edge pair
  Cell returnOtherCell(Cell cell) {
    if (cell.equals(this.node1)) {
      return this.node2;
    }
    return this.node1;
  }

  // boolean if cell is in an edge
  boolean containsCell(Cell cell) {
    return (this.node1.equals(cell) || this.node2.equals(cell));
  }

  // determines if two edges are equal
  @Override
  public boolean equals(Object o) {
    Edge edge = (Edge) o;
    return (edge.node1.equals(this.node1) && edge.node2.equals(this.node2))
        || (edge.node1.equals(this.node2) && edge.node2.equals(this.node1));
  }

  // creates edge hashcode
  @Override
  public int hashCode() {
    return 31 + this.node1.id.x + this.node1.id.y + this.node2.id.x + this.node2.id.y;
  }

}

//represents maze game 
class MazeWorld extends World {
  int boardWidth = 1000;
  int boardHeight = 600;

  int width;
  int height;

  int cellDimension;

  // currently displaying
  boolean currentlyDisplaying = false;

  ArrayList<ArrayList<Cell>> board;
  ArrayList<Edge> mst;
  WorldScene gameBoard;

  HashMap<Cell, Cell> representatives = new HashMap<Cell, Cell>();
  ArrayList<Edge> worklist = new ArrayList<Edge>();
  ArrayList<Cell> sets = new ArrayList<Cell>();

  Random rand;

  // cell solution path
  boolean pathFound = false;
  ArrayList<Cell> path = new ArrayList<Cell>();
  ArrayList<Cell> pathTempDisplay = new ArrayList<Cell>();
  int pathTempIndex = 0;

  // list of all cells searched
  ArrayList<Cell> searched = new ArrayList<Cell>();
  ArrayList<Cell> searchedTempDisplay = new ArrayList<Cell>();
  int searchedTempIndex = 0;

  HashMap<Cell, Edge> cameFromEdge;

  // constructor
  MazeWorld(int width, int height) {
    this.width = width;
    this.height = height;

    this.rand = new Random();

    this.cellDimension = this.boardWidth / this.width - 1;
    this.gameBoard = new WorldScene(this.boardWidth, this.boardHeight);
  }

  // constructor
  MazeWorld(int width, int height, int seed) {
    this(width, height);
    this.rand = new Random(seed);
  }

  // get width --> returns the width of the board so big bang knows how big to
  // draw board
  int getWidth() {
    return this.boardWidth;
  }

  // get height --> returns the height of the board so big bang knows how big to
  // draw board
  int getHeight() {
    return this.boardHeight;
  }

  // EFFECT: mutates board to include 2-d array of Cells
  // inits the board
  void initBoard() {
    this.board = new ArrayList<ArrayList<Cell>>();
    // 2d loops to populate board array
    for (int i = 0; i < this.height; i++) {
      ArrayList<Cell> row = new ArrayList<Cell>();
      for (int j = 0; j < this.width; j++) {
        Cell newNode = new Cell(new Posn(j, i));
        row.add(newNode);
        this.sets.add(newNode);
      }
      this.board.add(row);
    }
  }

  // inits cell neighbors and pairs between each cell and its neighbors in the
  // board
  void initEdges() {
    for (int i = 0; i < this.board.size(); i++) {
      for (int j = 0; j < this.board.get(i).size(); j++) {
        Cell cell = this.board.get(i).get(j);

        // Assign top neighbor
        if (i > 0) {
          Cell top = this.board.get(i - 1).get(j);
          cell.setTop(top);
          this.addEdge(top, cell);
        }

        // Assign bottom neighbor
        if (i < this.board.size() - 1) {
          Cell bottom = this.board.get(i + 1).get(j);
          cell.setBottom(bottom);
          this.addEdge(bottom, cell);
        }

        // Assign left neighbor
        if (j > 0) {
          Cell left = this.board.get(i).get(j - 1);
          cell.setLeft(left);
          this.addEdge(left, cell);
        }

        // Assign right neighbor
        if (j < this.board.get(i).size() - 1) {
          Cell right = this.board.get(i).get(j + 1);
          cell.setRight(right);
          this.addEdge(right, cell);
        }
      }
    }
  }

  // EFFECT: mutates edgesInTree to include new edge
  // takes two nodes adds them to list of all edges in board if not already added
  void addEdge(Cell c1, Cell c2) {
    // if there is no current Edge in edges in trees that has these two nodes, add
    // it with a random weight
    boolean edgeExists = false;
    for (Edge edge : this.worklist) {
      if (edge.containsBothNodes(c1, c2)) {
        edgeExists = true;
      }
    }

    if (!edgeExists) {
      int randWeight = rand.nextInt(this.width * this.height * 100);
      this.worklist.add(new Edge(c1, c2, randWeight));
    }
  }

  // implements union/find and returns a MST
  ArrayList<Edge> generateMaze() {
    ArrayList<Edge> edgesInTree = new ArrayList<Edge>();

    // sort edges by weight least to greatest
    this.worklist.sort(new Comparator<Edge>() {
      public int compare(Edge edge1, Edge edge2) {
        return Integer.compare(edge1.getWeight(), edge2.getWeight());
      }
    });

    // initialize every node to itself in the representatives
    this.initRepresentatives();

    while (this.worklist.size() > 0) {
      Edge workingEdge = this.worklist.get(0);
      this.worklist.remove(0);

      Cell cellOneRoot = this.getRoot(workingEdge.getNode1());
      Cell cellTwoRoot = this.getRoot(workingEdge.getNode2());

      if (!cellOneRoot.equals(cellTwoRoot)) {
        this.representatives.put(cellOneRoot, cellTwoRoot);
        edgesInTree.add(workingEdge);
      }
    }
    return edgesInTree;
  }

  // finds the root representive of a cell and returns it
  Cell getRoot(Cell cell) {
    if (!this.representatives.get(cell).equals(cell)) {
      return this.getRoot(this.representatives.get(cell));
    }

    return cell;
  }

  // EFFECT: mutates the representatives field
  // initializes representatives to themselves in a hash map
  void initRepresentatives() {
    for (Cell cell : this.sets) {
      this.representatives.put(cell, cell);
    }

  }

  // draws walls and returns world image of the walls
  WorldImage drawBoard() {
    WorldImage tempBoard = new EmptyImage();

    for (ArrayList<Cell> row : this.board) {
      WorldImage rowImage = new EmptyImage();
      for (Cell cell : row) {

        // sets the color of the cell according to its state
        Color c = Color.white;
        if (this.searchedTempDisplay.contains(cell)) {
          c = new Color(173, 216, 230);
        }
        if (this.pathTempDisplay.contains(cell)) {
          c = Color.blue;
        }

        // default cell without any borders
        WorldImage baseCellImage = new RectangleImage(this.cellDimension, this.cellDimension,
            OutlineMode.SOLID, c).movePinhole(0, cellDimension / 2);

        WorldImage bottomWall;
        WorldImage rightWall;

        WorldImage walls = new EmptyImage();

        boolean bottom = drawBottomWall(cell);
        boolean right = drawRightWall(cell);

        // if we need to draw both walls
        if (bottom && right) {
          bottomWall = new LineImage(new Posn(this.cellDimension, 0), Color.black);
          rightWall = new LineImage(new Posn(0, this.cellDimension), Color.black).movePinhole(0,
              this.cellDimension / 2);
          walls = new OverlayImage(bottomWall, baseCellImage).movePinhole(this.cellDimension / 2,
              0);
          walls = new OverlayImage(rightWall, walls).movePinhole(-this.cellDimension / 2,
              -this.cellDimension / 2);
        }
        // draw just bottom wall
        else if (bottom) {
          bottomWall = new LineImage(new Posn(this.cellDimension, 0), Color.black);
          walls = new OverlayImage(bottomWall, baseCellImage).movePinhole(0,
              -this.cellDimension / 2);
        }
        // draw just right wall
        else if (right) {
          rightWall = new LineImage(new Posn(0, this.cellDimension), Color.black).movePinhole(0,
              this.cellDimension / 2);
          baseCellImage = baseCellImage.movePinhole(this.cellDimension / 2, 0);
          walls = new OverlayImage(rightWall, baseCellImage).movePinhole(-this.cellDimension / 2,
              -this.cellDimension / 2);
        }
        // there are no walls to draw
        else {
          walls = baseCellImage.movePinhole(0, -this.cellDimension / 2);
        }

        // walls = new VisiblePinholeImage(walls);
        rowImage = new BesideImage(rowImage, walls);
      }

      tempBoard = new AboveImage(tempBoard, rowImage);
    }

    // add border wall
    tempBoard = new OverlayImage(new RectangleImage(this.cellDimension * this.width,
        this.cellDimension * this.height, OutlineMode.OUTLINE, Color.black), tempBoard);
    return tempBoard;
  }

  // returns true, if the cell should have a right wall barrier
  boolean drawRightWall(Cell cell) {
    boolean drawRight = true;

    Posn currentCellPosn = cell.id;
    Posn desiredCellPosn = new Posn(currentCellPosn.x + 1, currentCellPosn.y);

    // go through all the edges to check if this is a valid edge which can traversed
    for (Edge edge : this.mst) {
      // check to see if this edge is a connection between the current cell and the
      // cell to the right of it
      if ((new Utils().posnEqual(edge.node1.id, currentCellPosn)
          && new Utils().posnEqual(edge.node2.id, desiredCellPosn))
          || (new Utils().posnEqual(edge.node2.id, currentCellPosn)
              && new Utils().posnEqual(edge.node1.id, desiredCellPosn))) {
        drawRight = false;
      }
    }
    return drawRight;
  }

  // returns true, if the cell should have a bottom wall barrier
  boolean drawBottomWall(Cell cell) {
    boolean drawBottom = true;

    Posn currentCellPosn = cell.id;
    Posn desiredCellPosn = new Posn(currentCellPosn.x, currentCellPosn.y + 1);

    // go through all the edges to check if this is a valid edge which can traversed
    for (Edge edge : this.mst) {
      if ((new Utils().posnEqual(edge.node1.id, currentCellPosn)
          && new Utils().posnEqual(edge.node2.id, desiredCellPosn))
          || (new Utils().posnEqual(edge.node2.id, currentCellPosn)
              && new Utils().posnEqual(edge.node1.id, desiredCellPosn))) {
        drawBottom = false;
      }
    }

    return drawBottom;
  }

  // EFFECT: mutates searched to updates seen nodes, mutates path to hold the
  // solution path
  // breadth first search --> queue
  void breadthFirst() {
    // initialize variables
    this.searched = new ArrayList<Cell>();
    cameFromEdge = new HashMap<Cell, Edge>();
    ArrayDeque<Cell> worklist = new ArrayDeque<Cell>();

    Cell startingCell = board.get(0).get(0);
    Cell endingCell = board.get(height - 1).get(width - 1);

    worklist.add(startingCell);

    while (!worklist.isEmpty()) {
      Cell next = worklist.pollFirst();
      // if node has already been processed
      if (searched.contains(next)) {
        continue;
      }

      // if next node is the target node
      else if (next.equals(endingCell)) {
        // call the backtracking method
        // ***path done
        this.pathFound = true;
        this.path = this.reconstruct(cameFromEdge, next);

        // set display copies --> for visualization
        this.searchedTempIndex = 0;
        this.pathTempIndex = 0;
        this.pathTempDisplay = new ArrayList<Cell>();
        this.searchedTempDisplay = new ArrayList<Cell>();

        break;
      }

      else {
        for (Edge neighborEdge : this.getNeighborsInMST(next)) {
          Cell neighbor = neighborEdge.returnOtherCell(next);

          if (!searched.contains(neighbor)) {
            worklist.addLast(neighbor);
            cameFromEdge.put(neighbor, neighborEdge);
          }
        }
      }

      searched.add(next);
    }
  }

  // EFFECT: mutates searched to updates seen nodes, mutates path to hold the
  // solution path
  // depth first search --> queue
  void depthFirst() {
    // initialize variables
    this.searched = new ArrayList<Cell>();
    cameFromEdge = new HashMap<Cell, Edge>();
    ArrayDeque<Cell> worklist = new ArrayDeque<Cell>();

    Cell startingCell = board.get(0).get(0);
    Cell endingCell = board.get(height - 1).get(width - 1);

    worklist.add(startingCell);

    while (!worklist.isEmpty()) {
      Cell next = worklist.pop();
      // if node has already been processed
      if (searched.contains(next)) {
        continue;
      }

      // if next node is the target node
      else if (next.equals(endingCell)) {
        // call the backtracking method
        // ***path done
        this.pathFound = true;
        this.path = this.reconstruct(cameFromEdge, next);

        // set display copies --> for visualization
        this.searchedTempIndex = 0;
        this.pathTempIndex = 0;
        this.pathTempDisplay = new ArrayList<Cell>();
        this.searchedTempDisplay = new ArrayList<Cell>();

        break;
      }
      else {
        for (Edge neighborEdge : this.getNeighborsInMST(next)) {
          Cell neighbor = neighborEdge.returnOtherCell(next);

          if (!searched.contains(neighbor)) {
            worklist.push(neighbor);
            cameFromEdge.put(neighbor, neighborEdge);
          }
        }
      }

      searched.add(next);
    }
  }

  // goes back through the list and returns a path from the ending cell to the
  // start
  ArrayList<Cell> reconstruct(HashMap<Cell, Edge> cameFromEdge, Cell endingCell) {
    ArrayList<Cell> solution = new ArrayList<Cell>();

    Cell currentCell = endingCell;
    while (currentCell != this.board.get(0).get(0)) {
      solution.add(currentCell);
      currentCell = cameFromEdge.get(currentCell).returnOtherCell(currentCell);
    }
    solution.add(this.board.get(0).get(0));
    return solution;
  }

  // return traversable neighbors from a given cell in MST
  ArrayList<Edge> getNeighborsInMST(Cell next) {
    ArrayList<Edge> neighbors = new ArrayList<Edge>();

    for (Edge edge : this.mst) {
      if (edge.containsCell(next)) {
        neighbors.add(edge);
      }
    }
    return neighbors;
  }

  // depth first search --> stack

  // on tick method
  public void onTick() {

    // if still soliving path
    if (this.pathFound) {
      // if we are done
      if (this.searchedTempIndex + 1 == this.searched.size()) {
        this.searchedTempDisplay = this.searched;
        if (this.pathTempIndex + 1 == this.path.size()) {
          this.pathTempDisplay = this.path;
          this.endOfWorld("Path Found");
        }
        else {
          this.pathTempDisplay = new ArrayList<Cell>(this.path.subList(0, this.pathTempIndex++));
        }
      }
      else {
        this.searchedTempDisplay = new ArrayList<Cell>(
            this.searched.subList(0, this.searchedTempIndex++));
      }

    }
  }

  // handles key pressed events
  public void onKeyEvent(String key) {
    // restart the game at any time
    if (key.equals("r")) {
      this.initBoard();
      this.initEdges();
      this.mst = this.generateMaze();
      this.pathFound = false;
      this.searchedTempDisplay = new ArrayList<Cell>();
      this.pathTempDisplay = new ArrayList<Cell>();
      this.searched = new ArrayList<Cell>();
      this.path = new ArrayList<Cell>();
    }

    // if path not found allow user to choose between depth and breadth
    if (!this.pathFound) {
      // use breadth
      if (key.equals("b")) {
        this.breadthFirst();

      }
      // use depth
      if (key.equals("d")) {
        this.depthFirst();
      }
    }

    // if world hasnt ended, allow user to restart

  }

  // make scene method
  @Override
  public WorldScene makeScene() {
    gameBoard.placeImageXY(this.drawBoard(), this.boardWidth / 2, this.boardHeight / 2);
    return this.gameBoard;
  }
}

// to represent a utilities class
class Utils {

  // returns true if two positions are equal
  boolean posnEqual(Posn p1, Posn p2) {
    return (p1.equals(p2));
  }

}

// to represent examples class of the maze
class ExamplesMaze {

  // to represent examples of cells
  MazeWorld maze1;
  MazeWorld maze2;

  // to represent examples of cells
  Cell cell1 = new Cell(new Posn(0, 0));
  Cell cell1Rep = new Cell(new Posn(0, 0));
  Cell cell2 = new Cell(new Posn(1, 0));
  Cell cell2Rep = new Cell(new Posn(1, 0));
  Cell cell3 = new Cell(new Posn(0, 1));
  Cell cell3Rep = new Cell(new Posn(0, 1));
  Cell cell4 = new Cell(new Posn(1, 1));
  Cell cell4Rep = new Cell(new Posn(1, 1));

  // to represent examples of edges
  Edge edge1 = new Edge(cell1, cell2, 10);
  Edge edge2 = new Edge(cell2, cell3, 70);
  Edge edge3 = new Edge(cell3, cell4, 130);
  Edge edge4 = new Edge(cell4, cell1, 150);

  // to initiate all example FloodItWorlds used in tests and their fields
  void initTestExamples() {
    this.maze1 = new MazeWorld(1, 1, 2);
    this.maze2 = new MazeWorld(2, 2, 20);

    maze1.initBoard();
    maze1.initEdges();
    maze1.initRepresentatives();

    maze2.initBoard();
    maze2.initEdges();
    maze2.initRepresentatives();

  }

  // test methods for the Cell class
  // tests equals method
  void testCellEquals(Tester t) {
    this.initTestExamples();

    t.checkExpect(this.cell1.equals(this.cell1Rep), true);
    t.checkExpect(this.cell1.equals(this.cell2), false);
    t.checkExpect(this.cell2.equals(this.cell2Rep), true);
    t.checkExpect(this.cell2.equals(this.cell4), false);
    t.checkExpect(this.cell3.equals(this.cell3Rep), true);
    t.checkExpect(this.cell4.equals(this.cell4Rep), true);
    t.checkExpect(this.cell4.equals(this.cell2), false);

  }

  // tests hashCode method for cells
  void testCellHashCode(Tester t) {
    this.initTestExamples();

    t.checkExpect(this.cell1.hashCode(), 31);
    t.checkExpect(this.cell1Rep.hashCode(), 31);
    t.checkExpect(this.cell2.hashCode(), 32);
    t.checkExpect(this.cell3.hashCode(), 32);
    t.checkExpect(this.cell3Rep.hashCode(), 32);
    t.checkExpect(this.cell4.hashCode(), 33);
    t.checkExpect(this.cell4Rep.hashCode(), 33);
  }

  // to test the method setTop
  void testSetTop(Tester t) {
    this.initTestExamples();

    maze2.board.get(1).get(0).setTop(maze2.board.get(0).get(0));
    t.checkExpect(maze2.board.get(1).get(0).top, maze2.board.get(0).get(0));

    maze2.board.get(1).get(1).setTop(maze2.board.get(0).get(1));
    t.checkExpect(maze2.board.get(1).get(1).top, maze2.board.get(0).get(1));

  }

  // to test the method setBottom
  void testSetBottom(Tester t) {
    this.initTestExamples();

    maze2.board.get(0).get(0).setBottom(maze2.board.get(1).get(0));
    t.checkExpect(maze2.board.get(0).get(0).bottom, maze2.board.get(1).get(0));

    maze2.board.get(0).get(1).setBottom(maze2.board.get(1).get(1));
    t.checkExpect(maze2.board.get(0).get(1).bottom, maze2.board.get(1).get(1));

  }

  // to test the method setLeft
  void testSetLeft(Tester t) {
    this.initTestExamples();

    maze2.board.get(0).get(1).setLeft(maze2.board.get(0).get(0));
    t.checkExpect(maze2.board.get(0).get(1).left, maze2.board.get(0).get(0));

    maze2.board.get(1).get(1).setLeft(maze2.board.get(1).get(0));
    t.checkExpect(maze2.board.get(1).get(1).left, maze2.board.get(1).get(0));

  }

  // to test the method setRight
  void testSetRight(Tester t) {
    this.initTestExamples();

    maze2.board.get(0).get(0).setRight(maze2.board.get(0).get(1));
    t.checkExpect(maze2.board.get(0).get(0).right, maze2.board.get(0).get(1));

    maze2.board.get(1).get(0).setRight(maze2.board.get(1).get(1));
    t.checkExpect(maze2.board.get(1).get(0).right, maze2.board.get(1).get(1));
  }

  // methods of the class Edge
  // tests getWeight method
  void testGetWeight(Tester t) {
    t.checkExpect(edge1.getWeight(), 10);
    t.checkExpect(edge2.getWeight(), 70);
    t.checkExpect(edge3.getWeight(), 130);
    t.checkExpect(edge4.getWeight(), 150);
  }

  // tests getNode1 method
  void testGetNode1(Tester t) {
    t.checkExpect(edge1.getNode1(), cell1);
    t.checkExpect(edge2.getNode1(), cell2);
    t.checkExpect(edge3.getNode1(), cell3);
    t.checkExpect(edge4.getNode1(), cell4);
  }

  // tests getNode2 method
  void testGetNode2(Tester t) {
    t.checkExpect(edge1.getNode2(), cell2);
    t.checkExpect(edge2.getNode2(), cell3);
    t.checkExpect(edge3.getNode2(), cell4);
    t.checkExpect(edge4.getNode2(), cell1);
  }

  // tests containsBothNodes method
  void testContainsBothNodes(Tester t) {
    t.checkExpect(edge1.containsBothNodes(cell1, cell2), true);
    t.checkExpect(edge1.containsBothNodes(cell1, cell3), false);
    t.checkExpect(edge2.containsBothNodes(cell2, cell3), true);
    t.checkExpect(edge2.containsBothNodes(cell3, cell2), true);
    t.checkExpect(edge2.containsBothNodes(cell4, cell2), false);
    t.checkExpect(edge3.containsBothNodes(cell3, cell4), true);
    t.checkExpect(edge3.containsBothNodes(cell2, cell3), false);
    t.checkExpect(edge4.containsBothNodes(cell1, cell4), true);
    t.checkExpect(edge4.containsBothNodes(cell1, cell2), false);
  }

  // tests returnOtherCell method
  void testReturnOtherCell(Tester t) {
    t.checkExpect(edge1.returnOtherCell(cell1), cell2);
    t.checkExpect(edge1.returnOtherCell(cell2), cell1);
    t.checkExpect(edge2.returnOtherCell(cell2), cell3);
    t.checkExpect(edge2.returnOtherCell(cell3), cell2);
    t.checkExpect(edge3.returnOtherCell(cell3), cell4);
    t.checkExpect(edge3.returnOtherCell(cell4), cell3);
    t.checkExpect(edge4.returnOtherCell(cell4), cell1);
    t.checkExpect(edge4.returnOtherCell(cell1), cell4);
  }

  // tests containsCell method
  void testContainsCell(Tester t) {
    t.checkExpect(edge1.containsCell(cell1), true);
    t.checkExpect(edge1.containsCell(cell2), true);
    t.checkExpect(edge1.containsCell(cell3), false);
    t.checkExpect(edge2.containsCell(cell2), true);
    t.checkExpect(edge2.containsCell(cell1), false);
    t.checkExpect(edge3.containsCell(cell2), false);
    t.checkExpect(edge3.containsCell(cell4), true);
    t.checkExpect(edge3.containsCell(cell3), true);
    t.checkExpect(edge4.containsCell(cell1), true);
    t.checkExpect(edge4.containsCell(cell4), true);
  }

  // tests equals method
  void testEquals(Tester t) {
    t.checkExpect(edge1.equals(new Edge(cell1, cell2, 30)), true);
    t.checkExpect(edge1.equals(new Edge(cell2, cell1, 10)), true);
    t.checkExpect(edge1.equals(edge2), false);
    t.checkExpect(edge2.equals(new Edge(cell2, cell3, 30)), true);
    t.checkExpect(edge2.equals(edge2), true);
    t.checkExpect(edge2.equals(edge3), false);
    t.checkExpect(edge3.equals(new Edge(cell4, cell3, 130)), true);
    t.checkExpect(edge3.equals(edge1), false);
    t.checkExpect(edge4.equals(new Edge(cell4, cell1, 120)), true);
    t.checkExpect(edge4.equals(edge1), false);
  }

  // tests hashCode method for edges
  void testEdgeHashCode(Tester t) {
    this.initTestExamples();

    t.checkExpect(this.edge1.hashCode(), 32);
    t.checkExpect(this.edge2.hashCode(), 33);
    t.checkExpect(this.edge3.hashCode(), 34);
    t.checkExpect(this.edge4.hashCode(), 33);
  }

  // to test the methods of the class MazeWorld
  // tests getWidth method
  void testGetWidth(Tester t) {
    this.initTestExamples();

    t.checkExpect(maze1.getWidth(), 1000);
    t.checkExpect(maze2.getWidth(), 1000);
  }

  // tests getHeight method
  void testGetHeight(Tester t) {
    this.initTestExamples();

    t.checkExpect(maze1.getHeight(), 600);
    t.checkExpect(maze2.getHeight(), 600);
  }

  // tests the method initBoard
  void testInitBoard(Tester t) {
    this.initTestExamples();

    Cell testCell = new Cell(new Posn(0, 0));
    cell1.setRight(cell2);
    cell1.setBottom(cell3);
    cell2.setLeft(cell1);
    cell2.setBottom(cell4);
    cell3.setTop(cell1);
    cell3.setRight(cell4);
    cell4.setTop(cell2);
    cell4.setLeft(cell3);

    t.checkExpect(maze1.board, new ArrayList<ArrayList<Cell>>(
        Arrays.asList(new ArrayList<Cell>(Arrays.asList(testCell)))));

    t.checkExpect(maze2.board,
        new ArrayList<ArrayList<Cell>>(
            Arrays.asList(new ArrayList<Cell>(Arrays.asList(cell1, cell2)),

                new ArrayList<Cell>(Arrays.asList(cell3, cell4)))));
  }

  // tests initEdges method
  void testInitEdges(Tester t) {
    MazeWorld testMaze1 = new MazeWorld(2, 2, 15);
    testMaze1.initBoard();

    t.checkExpect(testMaze1.board.get(0).get(0).top, null);
    t.checkExpect(testMaze1.board.get(0).get(0).bottom, null);
    t.checkExpect(testMaze1.board.get(0).get(0).left, null);
    t.checkExpect(testMaze1.board.get(0).get(0).right, null);
    testMaze1.initEdges();
    t.checkExpect(testMaze1.board.get(0).get(0).top, null);
    t.checkExpect(testMaze1.board.get(0).get(0).bottom, testMaze1.board.get(1).get(0));
    t.checkExpect(testMaze1.board.get(0).get(0).left, null);
    t.checkExpect(testMaze1.board.get(0).get(0).right, testMaze1.board.get(0).get(1));

    MazeWorld testMaze2 = new MazeWorld(7, 9, 15);
    testMaze2.initBoard();

    t.checkExpect(testMaze2.board.get(2).get(4).top, null);
    t.checkExpect(testMaze2.board.get(2).get(4).bottom, null);
    t.checkExpect(testMaze2.board.get(2).get(4).left, null);
    t.checkExpect(testMaze2.board.get(2).get(4).right, null);
    testMaze2.initEdges();
    t.checkExpect(testMaze2.board.get(2).get(4).top, testMaze2.board.get(1).get(4));
    t.checkExpect(testMaze2.board.get(2).get(4).bottom, testMaze2.board.get(3).get(4));
    t.checkExpect(testMaze2.board.get(2).get(4).left, testMaze2.board.get(2).get(3));
    t.checkExpect(testMaze2.board.get(2).get(4).right, testMaze2.board.get(2).get(5));
  }

  // tests addEdge method
  void testAddEdge(Tester t) {
    MazeWorld testMaze1 = new MazeWorld(2, 2, 15);
    testMaze1.initBoard();

    t.checkExpect(testMaze1.worklist, new ArrayList<Edge>());
    testMaze1.addEdge(cell1, cell2);
    testMaze1.addEdge(cell2, cell3);
    testMaze1.addEdge(cell3, cell4);
    t.checkExpect(testMaze1.worklist, new ArrayList<Edge>(Arrays.asList(new Edge(cell1, cell2, 41),
        new Edge(cell2, cell3, 172), new Edge(cell3, cell4, 338))));

    MazeWorld testMaze2 = new MazeWorld(3, 4, 15);
    testMaze2.initBoard();

    t.checkExpect(testMaze2.worklist, new ArrayList<Edge>());
    testMaze2.addEdge(cell1, cell4);
    testMaze2.addEdge(cell2, cell3);
    testMaze2.addEdge(cell4, cell2);
    t.checkExpect(testMaze2.worklist, new ArrayList<Edge>(Arrays.asList(new Edge(cell1, cell4, 441),
        new Edge(cell2, cell3, 572), new Edge(cell4, cell2, 1138))));
  }

  // tests getRoot method
  void testGetRoot(Tester t) {
    this.initTestExamples();
    t.checkExpect(maze1.getRoot(maze1.board.get(0).get(0)), maze1.board.get(0).get(0));

    t.checkExpect(maze2.getRoot(maze2.board.get(0).get(0)), maze2.board.get(0).get(0));
    t.checkExpect(maze2.getRoot(maze2.board.get(1).get(0)), maze2.board.get(1).get(0));
    t.checkExpect(maze2.getRoot(maze2.board.get(0).get(1)), maze2.board.get(0).get(1));
    t.checkExpect(maze2.getRoot(maze2.board.get(1).get(1)), maze2.board.get(1).get(1));
  }

  // test initRepresentatives method
  void testInitRepresentatives(Tester t) {
    MazeWorld testMaze1 = new MazeWorld(2, 2, 15);
    testMaze1.initBoard();
    testMaze1.initEdges();

    t.checkExpect(testMaze1.representatives.get(testMaze1.board.get(0).get(0)), null);
    testMaze1.initRepresentatives();
    t.checkExpect(testMaze1.representatives.get(testMaze1.board.get(0).get(0)),
        testMaze1.board.get(0).get(0));

    MazeWorld testMaze2 = new MazeWorld(3, 4, 15);
    testMaze2.initBoard();

    t.checkExpect(testMaze2.representatives.get(testMaze2.board.get(0).get(0)), null);
    t.checkExpect(testMaze2.representatives.get(testMaze2.board.get(1).get(0)), null);
    t.checkExpect(testMaze2.representatives.get(testMaze2.board.get(0).get(1)), null);
    t.checkExpect(testMaze2.representatives.get(testMaze2.board.get(1).get(1)), null);
    testMaze2.initRepresentatives();
    t.checkExpect(testMaze2.representatives.get(testMaze2.board.get(0).get(0)),
        testMaze2.board.get(0).get(0));
    t.checkExpect(testMaze2.representatives.get(testMaze2.board.get(1).get(0)),
        testMaze2.board.get(1).get(0));
    t.checkExpect(testMaze2.representatives.get(testMaze2.board.get(0).get(1)),
        testMaze2.board.get(0).get(1));
    t.checkExpect(testMaze2.representatives.get(testMaze2.board.get(1).get(1)),
        testMaze2.board.get(1).get(1));
  }

  // test generateMaze
  void testGenerateMaze(Tester t) {
    MazeWorld game1 = new MazeWorld(2, 2, 5);
    game1.initBoard();
    game1.initEdges();
    game1.mst = game1.generateMaze();

    Edge edge1 = new Edge(new Cell(new Posn(1, 0)), new Cell(new Posn(1, 1)), 92);
    Edge edge2 = new Edge(new Cell(new Posn(1, 1)), new Cell(new Posn(0, 1)), 224);
    Edge edge3 = new Edge(new Cell(new Posn(1, 1)), new Cell(new Posn(1, 0)), 274);

    ArrayList<Edge> edges = new ArrayList<Edge>(Arrays.asList(edge1, edge2, edge3));

    for (Edge edge : edges) {
      boolean foundSameEdge = false;

      for (Edge edge_2 : game1.mst) {
        if (edge_2.containsBothNodes(edge.node1, edge.node2)) {
          foundSameEdge = true;
        }
      }
      t.checkExpect(foundSameEdge, true);
    }

    game1 = new MazeWorld(5, 3, 5);
    game1.initBoard();
    game1.initEdges();
    game1.mst = game1.generateMaze();

    Cell cell3 = new Cell(new Posn(2, 1));
    Cell cell4 = new Cell(new Posn(1, 1));
    Cell cell5 = new Cell(new Posn(0, 1));
    Cell cell6 = new Cell(new Posn(0, 0));
    Cell cell7 = new Cell(new Posn(1, 0));
    Cell cell8 = new Cell(new Posn(2, 0));
    Cell cell9 = new Cell(new Posn(3, 0));
    Cell cell10 = new Cell(new Posn(4, 0));
    Cell cell11 = new Cell(new Posn(4, 1));
    Cell cell12 = new Cell(new Posn(3, 1));
    Cell cell13 = new Cell(new Posn(3, 2));
    Cell cell14 = new Cell(new Posn(2, 2));
    Cell cell15 = new Cell(new Posn(1, 2));
    Cell cell16 = new Cell(new Posn(0, 2));
    Cell cell17 = new Cell(new Posn(4, 2));

    edge1 = new Edge(cell3, cell8, 6);
    edge2 = new Edge(cell15, cell16, 17);
    edge3 = new Edge(cell14, cell3, 60);
    Edge edge4 = new Edge(cell10, cell9, 191);
    Edge edge5 = new Edge(cell3, cell4, 247);
    Edge edge6 = new Edge(cell15, cell4, 303);
    Edge edge7 = new Edge(cell16, cell5, 321);
    Edge edge8 = new Edge(cell12, cell3, 428);
    Edge edge9 = new Edge(cell7, cell6, 592);
    Edge edge10 = new Edge(cell9, cell8, 605);
    Edge edge11 = new Edge(cell17, cell13, 665);
    Edge edge12 = new Edge(cell17, cell13, 665);
    Edge edge13 = new Edge(cell17, cell11, 715);
    Edge edge14 = new Edge(cell11, cell10, 772);
    Edge edge15 = new Edge(cell4, cell7, 974);

    ArrayList<Edge> edges2 = new ArrayList<Edge>(Arrays.asList(edge1, edge2, edge3, edge4, edge5,
        edge6, edge7, edge8, edge9, edge10, edge11, edge12, edge13, edge14, edge15));

    for (Edge edge : edges2) {
      boolean foundSameEdge = false;

      for (Edge edge_2 : game1.mst) {
        if (edge_2.containsBothNodes(edge.node1, edge.node2)) {
          foundSameEdge = true;
        }
      }
      t.checkExpect(foundSameEdge, true);
    }

  }

  // tests drawBoard method
  void testDrawBoard(Tester t) {
    MazeWorld game1 = new MazeWorld(1, 1, 2);
    game1.initBoard();
    game1.initEdges();
    game1.mst = game1.generateMaze();
    WorldImage baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension,
        OutlineMode.SOLID, Color.white).movePinhole(0, game1.cellDimension / 2);
    WorldImage bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    WorldImage rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black)
        .movePinhole(0, game1.cellDimension / 2);
    WorldImage walls = new OverlayImage(bottomWall, baseCellImage)
        .movePinhole(game1.cellDimension / 2, 0);
    walls = new OverlayImage(rightWall, walls).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    WorldImage rowImage = new BesideImage(new EmptyImage(), walls);
    WorldImage tempBoard = new AboveImage(new EmptyImage(), rowImage);
    tempBoard = new OverlayImage(new RectangleImage(game1.cellDimension * game1.width,
        game1.cellDimension * game1.height, OutlineMode.OUTLINE, Color.black), tempBoard);
    t.checkExpect(game1.drawBoard(), tempBoard);
    game1.breadthFirst();
    game1.searchedTempIndex = game1.searched.size() - 1;
    game1.pathTempIndex = game1.path.size() - 1;
    game1.pathTempDisplay = game1.path;
    game1.searchedTempDisplay = game1.searched;
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        new Color(0, 0, 255)).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    walls = new OverlayImage(bottomWall, baseCellImage).movePinhole(game1.cellDimension / 2, 0);
    walls = new OverlayImage(rightWall, walls).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(new EmptyImage(), walls);
    tempBoard = new AboveImage(new EmptyImage(), rowImage);
    tempBoard = new OverlayImage(new RectangleImage(game1.cellDimension * game1.width,
        game1.cellDimension * game1.height, OutlineMode.OUTLINE, Color.black), tempBoard);
    t.checkExpect(game1.drawBoard(), tempBoard);


    game1 = new MazeWorld(5, 3, 20);
    game1.initBoard();
    game1.initEdges();
    game1.mst = game1.generateMaze();

    // cell 0,0

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    WorldImage cellOne = baseCellImage.movePinhole(0, -game1.cellDimension / 2);
    rowImage = new BesideImage(new EmptyImage(), cellOne);

    // cell 0,1

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    WorldImage cellTwo = new OverlayImage(bottomWall, baseCellImage).movePinhole(0,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellTwo);

    // cell 0,2

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    walls = new OverlayImage(bottomWall, baseCellImage).movePinhole(game1.cellDimension / 2, 0);
    WorldImage cellThree = new OverlayImage(rightWall, walls).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellThree);

    // cell 0,3

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    baseCellImage = baseCellImage.movePinhole(game1.cellDimension / 2, 0);
    WorldImage cellFour = new OverlayImage(rightWall, baseCellImage)
        .movePinhole(-game1.cellDimension / 2, -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellFour);

    // cell 0,4

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    baseCellImage = baseCellImage.movePinhole(game1.cellDimension / 2, 0);
    WorldImage cellFive = new OverlayImage(rightWall, baseCellImage)
        .movePinhole(-game1.cellDimension / 2, -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellFive);
    tempBoard = new AboveImage(new EmptyImage(), rowImage);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    WorldImage cellSix = baseCellImage.movePinhole(0, -game1.cellDimension / 2);
    rowImage = new BesideImage(new EmptyImage(), cellSix);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);

    baseCellImage = baseCellImage.movePinhole(game1.cellDimension / 2, 0);
    WorldImage cellSeven = new OverlayImage(rightWall, baseCellImage)
        .movePinhole(-game1.cellDimension / 2, -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellSeven);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    WorldImage cellEight = new OverlayImage(bottomWall, baseCellImage).movePinhole(0,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellEight);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    baseCellImage = baseCellImage.movePinhole(game1.cellDimension / 2, 0);
    WorldImage cellNine = new OverlayImage(rightWall, baseCellImage)
        .movePinhole(-game1.cellDimension / 2, -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellNine);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    baseCellImage = baseCellImage.movePinhole(game1.cellDimension / 2, 0);
    WorldImage cellTen = new OverlayImage(rightWall, baseCellImage)
        .movePinhole(-game1.cellDimension / 2, -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellTen);
    tempBoard = new AboveImage(tempBoard, rowImage);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    walls = new OverlayImage(bottomWall, baseCellImage).movePinhole(game1.cellDimension / 2, 0);
    WorldImage cellEleven = new OverlayImage(rightWall, walls).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(new EmptyImage(), cellEleven);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    WorldImage cellTwelve = new OverlayImage(bottomWall, baseCellImage).movePinhole(0,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellTwelve);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    WorldImage cellThirteen = new OverlayImage(bottomWall, baseCellImage).movePinhole(0,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellThirteen);

    // cell 2,3

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    WorldImage cellFourteen = new OverlayImage(bottomWall, baseCellImage).movePinhole(0,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellFourteen);

    // cell 2,4

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    walls = new OverlayImage(bottomWall, baseCellImage).movePinhole(game1.cellDimension / 2, 0);
    WorldImage cellFifteen = new OverlayImage(rightWall, walls)
        .movePinhole(-game1.cellDimension / 2, -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellFifteen);
    tempBoard = new AboveImage(tempBoard, rowImage);
    tempBoard = new OverlayImage(new RectangleImage(game1.cellDimension * game1.width,
        game1.cellDimension * game1.height, OutlineMode.OUTLINE, Color.black), tempBoard);
    t.checkExpect(game1.drawBoard(), tempBoard);

    game1.breadthFirst();
    game1.searchedTempIndex = game1.searched.size() - 1;
    game1.pathTempIndex = game1.path.size() - 1;
    game1.pathTempDisplay = game1.path;
    game1.searchedTempDisplay = game1.searched;

    // cell 0,0

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.blue).movePinhole(0, game1.cellDimension / 2);
    cellOne = baseCellImage.movePinhole(0, -game1.cellDimension / 2);
    rowImage = new BesideImage(new EmptyImage(), cellOne);

    // cell 0,1

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        new Color(173, 216, 230)).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    cellTwo = new OverlayImage(bottomWall, baseCellImage).movePinhole(0, -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellTwo);

    // cell 0,2

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        new Color(173, 216, 230)).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    walls = new OverlayImage(bottomWall, baseCellImage).movePinhole(game1.cellDimension / 2, 0);
    cellThree = new OverlayImage(rightWall, walls).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellThree);

    // cell 0,3

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    baseCellImage = baseCellImage.movePinhole(game1.cellDimension / 2, 0);
    cellFour = new OverlayImage(rightWall, baseCellImage).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellFour);

    // cell 0,4

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    baseCellImage = baseCellImage.movePinhole(game1.cellDimension / 2, 0);
    cellFive = new OverlayImage(rightWall, baseCellImage).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellFive);
    tempBoard = new AboveImage(new EmptyImage(), rowImage);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.blue).movePinhole(0, game1.cellDimension / 2);
    cellSix = baseCellImage.movePinhole(0, -game1.cellDimension / 2);
    rowImage = new BesideImage(new EmptyImage(), cellSix);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.blue).movePinhole(0, game1.cellDimension / 2);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    baseCellImage = baseCellImage.movePinhole(game1.cellDimension / 2, 0);
    cellSeven = new OverlayImage(rightWall, baseCellImage).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellSeven);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    cellEight = new OverlayImage(bottomWall, baseCellImage).movePinhole(0,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellEight);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    baseCellImage = baseCellImage.movePinhole(game1.cellDimension / 2, 0);
    cellNine = new OverlayImage(rightWall, baseCellImage).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellNine);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    baseCellImage = baseCellImage.movePinhole(game1.cellDimension / 2, 0);
    cellTen = new OverlayImage(rightWall, baseCellImage).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellTen);
    tempBoard = new AboveImage(tempBoard, rowImage);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        new Color(173, 216, 230)).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    walls = new OverlayImage(bottomWall, baseCellImage).movePinhole(game1.cellDimension / 2, 0);
    cellEleven = new OverlayImage(rightWall, walls).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(new EmptyImage(), cellEleven);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.blue).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    cellTwelve = new OverlayImage(bottomWall, baseCellImage).movePinhole(0,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellTwelve);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.blue).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    cellThirteen = new OverlayImage(bottomWall, baseCellImage).movePinhole(0,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellThirteen);

    // cell 2,3

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.blue).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    cellFourteen = new OverlayImage(bottomWall, baseCellImage).movePinhole(0,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellFourteen);

    // cell 2,4

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.blue).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    walls = new OverlayImage(bottomWall, baseCellImage).movePinhole(game1.cellDimension / 2, 0);
    cellFifteen = new OverlayImage(rightWall, walls).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellFifteen);
    tempBoard = new AboveImage(tempBoard, rowImage);
    tempBoard = new OverlayImage(new RectangleImage(game1.cellDimension * game1.width,
        game1.cellDimension * game1.height, OutlineMode.OUTLINE, Color.black), tempBoard);
    t.checkExpect(game1.drawBoard(), tempBoard);

    game1 = new MazeWorld(5, 3, 20);
    game1.initBoard();
    game1.initEdges();
    game1.mst = game1.generateMaze();
    game1.depthFirst();
    game1.searchedTempIndex = game1.searched.size() - 1;
    game1.pathTempIndex = game1.path.size() - 1;
    game1.pathTempDisplay = game1.path;
    game1.searchedTempDisplay = game1.searched;

    // cell 0,0

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.blue).movePinhole(0, game1.cellDimension / 2);
    cellOne = baseCellImage.movePinhole(0, -game1.cellDimension / 2);

    rowImage = new BesideImage(new EmptyImage(), cellOne);

    // cell 0,1

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        new Color(173, 216, 230)).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    cellTwo = new OverlayImage(bottomWall, baseCellImage).movePinhole(0, -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellTwo);

    // cell 0,2

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        new Color(173, 216, 230)).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    walls = new OverlayImage(bottomWall, baseCellImage).movePinhole(game1.cellDimension / 2, 0);
    cellThree = new OverlayImage(rightWall, walls).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellThree);

    // cell 0,3

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        new Color(173, 216, 230)).movePinhole(0, game1.cellDimension / 2);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    baseCellImage = baseCellImage.movePinhole(game1.cellDimension / 2, 0);
    cellFour = new OverlayImage(rightWall, baseCellImage).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellFour);

    // cell 0,4

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    baseCellImage = baseCellImage.movePinhole(game1.cellDimension / 2, 0);
    cellFive = new OverlayImage(rightWall, baseCellImage).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellFive);
    tempBoard = new AboveImage(new EmptyImage(), rowImage);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.blue).movePinhole(0, game1.cellDimension / 2);
    cellSix = baseCellImage.movePinhole(0, -game1.cellDimension / 2);
    rowImage = new BesideImage(new EmptyImage(), cellSix);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.blue).movePinhole(0, game1.cellDimension / 2);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    baseCellImage = baseCellImage.movePinhole(game1.cellDimension / 2, 0);
    cellSeven = new OverlayImage(rightWall, baseCellImage).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellSeven);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        new Color(173, 216, 230)).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    cellEight = new OverlayImage(bottomWall, baseCellImage).movePinhole(0,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellEight);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        new Color(173, 216, 230)).movePinhole(0, game1.cellDimension / 2);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    baseCellImage = baseCellImage.movePinhole(game1.cellDimension / 2, 0);
    cellNine = new OverlayImage(rightWall, baseCellImage).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellNine);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    baseCellImage = baseCellImage.movePinhole(game1.cellDimension / 2, 0);
    cellTen = new OverlayImage(rightWall, baseCellImage).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellTen);
    tempBoard = new AboveImage(tempBoard, rowImage);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        new Color(173, 216, 230)).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    walls = new OverlayImage(bottomWall, baseCellImage).movePinhole(game1.cellDimension / 2, 0);
    cellEleven = new OverlayImage(rightWall, walls).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(new EmptyImage(), cellEleven);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.blue).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    cellTwelve = new OverlayImage(bottomWall, baseCellImage).movePinhole(0,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellTwelve);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.blue).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    cellThirteen = new OverlayImage(bottomWall, baseCellImage).movePinhole(0,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellThirteen);

    // cell 2,3

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.blue).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    cellFourteen = new OverlayImage(bottomWall, baseCellImage).movePinhole(0,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellFourteen);

    // cell 2,4

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.blue).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    walls = new OverlayImage(bottomWall, baseCellImage).movePinhole(game1.cellDimension / 2, 0);
    cellFifteen = new OverlayImage(rightWall, walls).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellFifteen);
    tempBoard = new AboveImage(tempBoard, rowImage);
    tempBoard = new OverlayImage(new RectangleImage(game1.cellDimension * game1.width,
        game1.cellDimension * game1.height, OutlineMode.OUTLINE, Color.black), tempBoard);

    t.checkExpect(game1.drawBoard(), tempBoard);

  }

  // tests the method drawRightWall
  void testDrawRightWall(Tester t) {
    MazeWorld game1 = new MazeWorld(1, 1, 2);
    game1.initBoard();
    game1.initEdges();
    game1.mst = game1.generateMaze();

    t.checkExpect(game1.drawRightWall(game1.board.get(0).get(0)), true);

    game1 = new MazeWorld(5, 3, 20);
    game1.initBoard();
    game1.initEdges();
    game1.mst = game1.generateMaze();

    t.checkExpect(game1.drawRightWall(game1.board.get(0).get(0)), false);
    t.checkExpect(game1.drawRightWall(game1.board.get(1).get(0)), false);
    t.checkExpect(game1.drawRightWall(game1.board.get(2).get(2)), false);
    t.checkExpect(game1.drawRightWall(game1.board.get(1).get(2)), false);
    t.checkExpect(game1.drawRightWall(game1.board.get(1).get(1)), true);

  }

  // tests the method drawBottomWall
  void testDrawBottomWall(Tester t) {
    MazeWorld game1 = new MazeWorld(1, 1, 2);
    game1.initBoard();
    game1.initEdges();
    game1.mst = game1.generateMaze();

    t.checkExpect(game1.drawBottomWall(game1.board.get(0).get(0)), true);

    game1 = new MazeWorld(5, 3, 20);
    game1.initBoard();
    game1.initEdges();
    game1.mst = game1.generateMaze();

    t.checkExpect(game1.drawBottomWall(game1.board.get(0).get(0)), false);
    t.checkExpect(game1.drawBottomWall(game1.board.get(1).get(0)), false);
    t.checkExpect(game1.drawBottomWall(game1.board.get(2).get(2)), true);
    t.checkExpect(game1.drawBottomWall(game1.board.get(1).get(2)), true);
    t.checkExpect(game1.drawBottomWall(game1.board.get(1).get(1)), false);

  }

  // tests breadth first search method
  void testBreadthFirst(Tester t) {
    MazeWorld game = new MazeWorld(2, 2, 29);
    game.initBoard();
    game.initEdges();
    game.mst = game.generateMaze();

    t.checkExpect(game.path.size() == 0, true);
    t.checkExpect(game.searched.size() == 0, true);
    game.breadthFirst();
    Cell cell1 = new Cell(new Posn(1, 1));
    Cell cell2 = new Cell(new Posn(0, 1));
    Cell cell3 = new Cell(new Posn(0, 0));
    ArrayList<Cell> pathResult1 = new ArrayList<Cell>(Arrays.asList(cell1, cell2, cell3));
    int pathResult1Index = 0;
    for (Cell c : game.path) {
      t.checkExpect(c.equals(pathResult1.get(pathResult1Index++)), true);
    }

    MazeWorld game1 = new MazeWorld(5, 3, 25);
    game1.initBoard();
    game1.initEdges();
    game1.mst = game1.generateMaze();

    t.checkExpect(game1.path.size() == 0, true);
    t.checkExpect(game1.searched.size() == 0, true);

    game1.breadthFirst();
    cell1 = new Cell(new Posn(4, 2));
    cell2 = new Cell(new Posn(3, 2));
    cell3 = new Cell(new Posn(2, 2));
    Cell cell4 = new Cell(new Posn(2, 1));
    Cell cell5 = new Cell(new Posn(2, 0));
    Cell cell6 = new Cell(new Posn(1, 0));
    Cell cell7 = new Cell(new Posn(0, 0));
    ArrayList<Cell> pathResult = new ArrayList<Cell>(
        Arrays.asList(cell1, cell2, cell3, cell4, cell5, cell6, cell7));
    int pathResultIndex = 0;
    for (Cell c : game1.path) {
      t.checkExpect(c.equals(pathResult.get(pathResultIndex++)), true);
    }

    cell1 = new Cell(new Posn(0, 0));
    cell2 = new Cell(new Posn(1, 0));
    cell3 = new Cell(new Posn(2, 0));
    cell4 = new Cell(new Posn(1, 1));
    cell5 = new Cell(new Posn(2, 1));
    cell6 = new Cell(new Posn(3, 0));
    cell7 = new Cell(new Posn(1, 2));
    Cell cell8 = new Cell(new Posn(2, 2));
    Cell cell9 = new Cell(new Posn(3, 1));
    Cell cell10 = new Cell(new Posn(0, 2));
    Cell cell11 = new Cell(new Posn(3, 2));
    Cell cell12 = new Cell(new Posn(4, 1));
    Cell cell13 = new Cell(new Posn(0, 1));
    ArrayList<Cell> searchedResult = new ArrayList<Cell>(Arrays.asList(cell1, cell2, cell3, cell4,
        cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13));
    int searchedResultIndex = 0;
    for (Cell c : game1.searched) {
      t.checkExpect(c.equals(searchedResult.get(searchedResultIndex++)), true);
    }
  }

  // tests depth first search method
  void testDepthFirst(Tester t) {
    MazeWorld game = new MazeWorld(2, 2, 29);
    game.initBoard();
    game.initEdges();
    game.mst = game.generateMaze();
    t.checkExpect(game.path.size() == 0, true);
    t.checkExpect(game.searched.size() == 0, true);
    game.depthFirst();
    Cell cell1 = new Cell(new Posn(1, 1));
    Cell cell2 = new Cell(new Posn(0, 1));
    Cell cell3 = new Cell(new Posn(0, 0));
    ArrayList<Cell> pathResult1 = new ArrayList<Cell>(Arrays.asList(cell1, cell2, cell3));
    int pathResult1Index = 0;
    for (Cell c : game.path) {
      t.checkExpect(c.equals(pathResult1.get(pathResult1Index++)), true);
    }
    MazeWorld game1 = new MazeWorld(5, 3, 25);
    game1.initBoard();
    game1.initEdges();
    game1.mst = game1.generateMaze();
    t.checkExpect(game1.path.size() == 0, true);
    t.checkExpect(game1.searched.size() == 0, true);
    game1.depthFirst();
    cell1 = new Cell(new Posn(4, 2));
    cell2 = new Cell(new Posn(3, 2));
    cell3 = new Cell(new Posn(2, 2));
    Cell cell4 = new Cell(new Posn(2, 1));
    Cell cell5 = new Cell(new Posn(2, 0));
    Cell cell6 = new Cell(new Posn(1, 0));
    Cell cell7 = new Cell(new Posn(0, 0));
    ArrayList<Cell> pathResult = new ArrayList<Cell>(
        Arrays.asList(cell1, cell2, cell3, cell4, cell5, cell6, cell7));
    int pathResultIndex = 0;
    for (Cell c : game1.path) {
      t.checkExpect(c.equals(pathResult.get(pathResultIndex++)), true);
    }
    cell1 = new Cell(new Posn(0, 0));
    cell2 = new Cell(new Posn(1, 0));
    cell3 = new Cell(new Posn(1, 1));
    cell4 = new Cell(new Posn(1, 2));
    cell5 = new Cell(new Posn(0, 2));
    cell6 = new Cell(new Posn(0, 1));
    cell7 = new Cell(new Posn(2, 0));
    Cell cell8 = new Cell(new Posn(3, 0));
    Cell cell9 = new Cell(new Posn(3, 1));
    Cell cell10 = new Cell(new Posn(4, 1));
    Cell cell11 = new Cell(new Posn(4, 0));
    Cell cell12 = new Cell(new Posn(2, 1));
    Cell cell13 = new Cell(new Posn(2, 2));
    Cell cell14 = new Cell(new Posn(3, 2));
    ArrayList<Cell> searchedResult = new ArrayList<Cell>(Arrays.asList(cell1, cell2, cell3, cell4,
        cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14));
    int searchedResultIndex = 0;
    for (Cell c : game1.searched) {
      t.checkExpect(c.equals(searchedResult.get(searchedResultIndex++)), true);
    }
  }

  // tests reconstruct method
  void testReconstruct(Tester t) {
    MazeWorld testMaze1 = new MazeWorld(2, 2, 15);
    testMaze1.initBoard();
    testMaze1.initEdges();
    testMaze1.mst = testMaze1.generateMaze();
    testMaze1.depthFirst();

    t.checkExpect(testMaze1.reconstruct(testMaze1.cameFromEdge, testMaze1.board.get(1).get(1)),
        new ArrayList<Cell>(Arrays.asList(testMaze1.board.get(1).get(1),
            testMaze1.board.get(1).get(0), testMaze1.board.get(0).get(0))));

    MazeWorld testMaze2 = new MazeWorld(5, 3, 15);
    testMaze2.initBoard();
    testMaze2.initEdges();
    testMaze2.mst = testMaze2.generateMaze();
    testMaze2.breadthFirst();

    t.checkExpect(testMaze2.reconstruct(testMaze2.cameFromEdge, testMaze2.board.get(2).get(4)),

        new ArrayList<Cell>(Arrays.asList(testMaze2.board.get(2).get(4),
            testMaze2.board.get(1).get(4), testMaze2.board.get(1).get(3),
            testMaze2.board.get(1).get(2), testMaze2.board.get(1).get(1),
            testMaze2.board.get(1).get(0), testMaze2.board.get(0).get(0))));
  }

  // tests getNeighborsInMST method
  void testGetNeighborsInMST(Tester t) {
    MazeWorld testMaze1 = new MazeWorld(2, 2, 15);
    testMaze1.initBoard();
    testMaze1.initEdges();
    testMaze1.mst = testMaze1.generateMaze();

    t.checkExpect(testMaze1.getNeighborsInMST(testMaze1.board.get(1).get(1)),
        new ArrayList<Edge>(Arrays
            .asList(new Edge(testMaze1.board.get(1).get(1), testMaze1.board.get(1).get(0), 267))));

    MazeWorld testMaze2 = new MazeWorld(5, 3, 15);
    testMaze2.initBoard();
    testMaze2.initEdges();
    testMaze2.mst = testMaze2.generateMaze();

    t.checkExpect(testMaze2.getNeighborsInMST(testMaze2.board.get(2).get(1)),
        new ArrayList<Edge>(Arrays.asList(
            new Edge(testMaze2.board.get(2).get(1), testMaze2.board.get(1).get(1), 577),
            new Edge(testMaze2.board.get(2).get(1), testMaze2.board.get(2).get(0), 649))));

  }

  // tests key pressed method
  void testKeyPressed(Tester t) {

    MazeWorld game1 = new MazeWorld(2, 2, 5);
    game1.initBoard();
    game1.initEdges();
    game1.mst = game1.generateMaze();

    game1.onKeyEvent("r");
    t.checkExpect(game1.path.size(), 0);
    t.checkExpect(game1.searched.size(), 0);
    t.checkExpect(game1.searchedTempDisplay.size(), 0);
    t.checkExpect(game1.pathTempDisplay.size(), 0);
    t.checkExpect(game1.pathFound, false);

    game1.onKeyEvent("b");
    Cell cell1 = new Cell(new Posn(1, 1));
    Cell cell2 = new Cell(new Posn(1, 0));
    Cell cell3 = new Cell(new Posn(0, 0));
    ArrayList<Cell> pathResult1 = new ArrayList<Cell>(Arrays.asList(cell1, cell2, cell3));
    int pathResult1Index = 0;
    for (Cell c : game1.path) {
      t.checkExpect(c.equals(pathResult1.get(pathResult1Index++)), true);
    }

    game1.onKeyEvent("d");
    cell1 = new Cell(new Posn(1, 1));
    cell2 = new Cell(new Posn(1, 0));
    cell3 = new Cell(new Posn(0, 0));
    pathResult1 = new ArrayList<Cell>(Arrays.asList(cell1, cell2, cell3));
    pathResult1Index = 0;
    for (Cell c : game1.path) {
      t.checkExpect(c.equals(pathResult1.get(pathResult1Index++)), true);
    }

    game1 = new MazeWorld(3, 2, 10);
    game1.initBoard();
    game1.initEdges();
    game1.mst = game1.generateMaze();
    game1.onKeyEvent("r");

    t.checkExpect(game1.path.size(), 0);
    t.checkExpect(game1.searched.size(), 0);
    t.checkExpect(game1.searchedTempDisplay.size(), 0);
    t.checkExpect(game1.pathTempDisplay.size(), 0);
    t.checkExpect(game1.pathFound, false);

    game1.onKeyEvent("b");
    cell1 = new Cell(new Posn(2, 1));
    cell2 = new Cell(new Posn(1, 1));
    cell3 = new Cell(new Posn(1, 0));
    Cell cell4 = new Cell(new Posn(0, 0));
    pathResult1 = new ArrayList<Cell>(Arrays.asList(cell1, cell2, cell3, cell4));
    pathResult1Index = 0;
    for (Cell c : game1.path) {
      t.checkExpect(c.equals(pathResult1.get(pathResult1Index++)), true);
    }

    game1.onKeyEvent("d");
    cell1 = new Cell(new Posn(2, 1));
    cell2 = new Cell(new Posn(1, 1));
    cell3 = new Cell(new Posn(1, 0));
    cell4 = new Cell(new Posn(0, 0));
    pathResult1 = new ArrayList<Cell>(Arrays.asList(cell1, cell2, cell3, cell4));
    pathResult1Index = 0;
    for (Cell c : game1.path) {
      System.out.println(c.id);
      t.checkExpect(c.equals(pathResult1.get(pathResult1Index++)), true);
    }
  }

  // tests the method makeScene
  void testMakeScene(Tester t) {
    MazeWorld game1 = new MazeWorld(1, 1, 2);
    game1.initBoard();
    game1.initEdges();
    game1.mst = game1.generateMaze();

    WorldImage baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension,
        OutlineMode.SOLID, Color.white).movePinhole(0, game1.cellDimension / 2);
    WorldImage bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    WorldImage rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black)
        .movePinhole(0, game1.cellDimension / 2);
    WorldImage walls = new OverlayImage(bottomWall, baseCellImage)
        .movePinhole(game1.cellDimension / 2, 0);
    walls = new OverlayImage(rightWall, walls).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    WorldImage rowImage = new BesideImage(new EmptyImage(), walls);
    WorldImage tempBoard = new AboveImage(new EmptyImage(), rowImage);
    tempBoard = new OverlayImage(new RectangleImage(game1.cellDimension * game1.width,
        game1.cellDimension * game1.height, OutlineMode.OUTLINE, Color.black), tempBoard);
    game1.gameBoard.placeImageXY(tempBoard, 500, 300);

    t.checkExpect(game1.makeScene(), game1.gameBoard);

    game1 = new MazeWorld(5, 3, 20);
    game1.initBoard();
    game1.initEdges();
    game1.mst = game1.generateMaze();

    // cell 0,0
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    WorldImage cellOne = baseCellImage.movePinhole(0, -game1.cellDimension / 2);
    rowImage = new BesideImage(new EmptyImage(), cellOne);

    // cell 0,1
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    WorldImage cellTwo = new OverlayImage(bottomWall, baseCellImage).movePinhole(0,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellTwo);

    // cell 0,2
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    walls = new OverlayImage(bottomWall, baseCellImage).movePinhole(game1.cellDimension / 2, 0);
    WorldImage cellThree = new OverlayImage(rightWall, walls).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellThree);

    // cell 0,3
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    baseCellImage = baseCellImage.movePinhole(game1.cellDimension / 2, 0);
    WorldImage cellFour = new OverlayImage(rightWall, baseCellImage)
        .movePinhole(-game1.cellDimension / 2, -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellFour);

    // cell 0,4
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    baseCellImage = baseCellImage.movePinhole(game1.cellDimension / 2, 0);
    WorldImage cellFive = new OverlayImage(rightWall, baseCellImage)
        .movePinhole(-game1.cellDimension / 2, -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellFive);

    tempBoard = new AboveImage(new EmptyImage(), rowImage);

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    WorldImage cellSix = baseCellImage.movePinhole(0, -game1.cellDimension / 2);
    rowImage = new BesideImage(new EmptyImage(), cellSix);

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    baseCellImage = baseCellImage.movePinhole(game1.cellDimension / 2, 0);
    WorldImage cellSeven = new OverlayImage(rightWall, baseCellImage)
        .movePinhole(-game1.cellDimension / 2, -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellSeven);

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    WorldImage cellEight = new OverlayImage(bottomWall, baseCellImage).movePinhole(0,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellEight);

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    baseCellImage = baseCellImage.movePinhole(game1.cellDimension / 2, 0);
    WorldImage cellNine = new OverlayImage(rightWall, baseCellImage)
        .movePinhole(-game1.cellDimension / 2, -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellNine);

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    baseCellImage = baseCellImage.movePinhole(game1.cellDimension / 2, 0);
    WorldImage cellTen = new OverlayImage(rightWall, baseCellImage)
        .movePinhole(-game1.cellDimension / 2, -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellTen);

    tempBoard = new AboveImage(tempBoard, rowImage);

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    walls = new OverlayImage(bottomWall, baseCellImage).movePinhole(game1.cellDimension / 2, 0);
    WorldImage cellEleven = new OverlayImage(rightWall, walls).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(new EmptyImage(), cellEleven);

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    WorldImage cellTwelve = new OverlayImage(bottomWall, baseCellImage).movePinhole(0,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellTwelve);

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    WorldImage cellThirteen = new OverlayImage(bottomWall, baseCellImage).movePinhole(0,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellThirteen);

    // cell 2,3
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    WorldImage cellFourteen = new OverlayImage(bottomWall, baseCellImage).movePinhole(0,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellFourteen);

    // cell 2,4
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    walls = new OverlayImage(bottomWall, baseCellImage).movePinhole(game1.cellDimension / 2, 0);
    WorldImage cellFifteen = new OverlayImage(rightWall, walls)
        .movePinhole(-game1.cellDimension / 2, -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellFifteen);

    tempBoard = new AboveImage(tempBoard, rowImage);

    tempBoard = new OverlayImage(new RectangleImage(game1.cellDimension * game1.width,
        game1.cellDimension * game1.height, OutlineMode.OUTLINE, Color.black), tempBoard);

    game1.gameBoard.placeImageXY(tempBoard, 500, 300);

    t.checkExpect(game1.makeScene(), game1.gameBoard);

    game1.breadthFirst();
    game1.searchedTempIndex = game1.searched.size() - 1;
    game1.pathTempIndex = game1.path.size() - 1;
    game1.pathTempDisplay = game1.path;
    game1.searchedTempDisplay = game1.searched;

    // cell 0,0

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.blue).movePinhole(0, game1.cellDimension / 2);
    cellOne = baseCellImage.movePinhole(0, -game1.cellDimension / 2);
    rowImage = new BesideImage(new EmptyImage(), cellOne);

    // cell 0,1

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        new Color(173, 216, 230)).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    cellTwo = new OverlayImage(bottomWall, baseCellImage).movePinhole(0, -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellTwo);

    // cell 0,2

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        new Color(173, 216, 230)).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    walls = new OverlayImage(bottomWall, baseCellImage).movePinhole(game1.cellDimension / 2, 0);
    cellThree = new OverlayImage(rightWall, walls).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellThree);

    // cell 0,3

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    baseCellImage = baseCellImage.movePinhole(game1.cellDimension / 2, 0);
    cellFour = new OverlayImage(rightWall, baseCellImage).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellFour);

    // cell 0,4

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    baseCellImage = baseCellImage.movePinhole(game1.cellDimension / 2, 0);
    cellFive = new OverlayImage(rightWall, baseCellImage).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellFive);
    tempBoard = new AboveImage(new EmptyImage(), rowImage);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.blue).movePinhole(0, game1.cellDimension / 2);
    cellSix = baseCellImage.movePinhole(0, -game1.cellDimension / 2);
    rowImage = new BesideImage(new EmptyImage(), cellSix);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.blue).movePinhole(0, game1.cellDimension / 2);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    baseCellImage = baseCellImage.movePinhole(game1.cellDimension / 2, 0);
    cellSeven = new OverlayImage(rightWall, baseCellImage).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellSeven);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    cellEight = new OverlayImage(bottomWall, baseCellImage).movePinhole(0,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellEight);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    baseCellImage = baseCellImage.movePinhole(game1.cellDimension / 2, 0);
    cellNine = new OverlayImage(rightWall, baseCellImage).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellNine);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    baseCellImage = baseCellImage.movePinhole(game1.cellDimension / 2, 0);
    cellTen = new OverlayImage(rightWall, baseCellImage).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellTen);
    tempBoard = new AboveImage(tempBoard, rowImage);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        new Color(173, 216, 230)).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    walls = new OverlayImage(bottomWall, baseCellImage).movePinhole(game1.cellDimension / 2, 0);
    cellEleven = new OverlayImage(rightWall, walls).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(new EmptyImage(), cellEleven);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.blue).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    cellTwelve = new OverlayImage(bottomWall, baseCellImage).movePinhole(0,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellTwelve);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.blue).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    cellThirteen = new OverlayImage(bottomWall, baseCellImage).movePinhole(0,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellThirteen);

    // cell 2,3

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.blue).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    cellFourteen = new OverlayImage(bottomWall, baseCellImage).movePinhole(0,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellFourteen);

    // cell 2,4

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.blue).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    walls = new OverlayImage(bottomWall, baseCellImage).movePinhole(game1.cellDimension / 2, 0);
    cellFifteen = new OverlayImage(rightWall, walls).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellFifteen);
    tempBoard = new AboveImage(tempBoard, rowImage);
    tempBoard = new OverlayImage(new RectangleImage(game1.cellDimension * game1.width,
        game1.cellDimension * game1.height, OutlineMode.OUTLINE, Color.black), tempBoard);

    t.checkExpect(game1.makeScene(), game1.gameBoard);

    game1 = new MazeWorld(5, 3, 20);
    game1.initBoard();
    game1.initEdges();
    game1.mst = game1.generateMaze();
    game1.depthFirst();
    game1.searchedTempIndex = game1.searched.size() - 1;
    game1.pathTempIndex = game1.path.size() - 1;
    game1.pathTempDisplay = game1.path;
    game1.searchedTempDisplay = game1.searched;

    // cell 0,0

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.blue).movePinhole(0, game1.cellDimension / 2);
    cellOne = baseCellImage.movePinhole(0, -game1.cellDimension / 2);

    rowImage = new BesideImage(new EmptyImage(), cellOne);

    // cell 0,1

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        new Color(173, 216, 230)).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    cellTwo = new OverlayImage(bottomWall, baseCellImage).movePinhole(0, -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellTwo);

    // cell 0,2

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        new Color(173, 216, 230)).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    walls = new OverlayImage(bottomWall, baseCellImage).movePinhole(game1.cellDimension / 2, 0);
    cellThree = new OverlayImage(rightWall, walls).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellThree);

    // cell 0,3

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        new Color(173, 216, 230)).movePinhole(0, game1.cellDimension / 2);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    baseCellImage = baseCellImage.movePinhole(game1.cellDimension / 2, 0);
    cellFour = new OverlayImage(rightWall, baseCellImage).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellFour);

    // cell 0,4

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    baseCellImage = baseCellImage.movePinhole(game1.cellDimension / 2, 0);
    cellFive = new OverlayImage(rightWall, baseCellImage).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellFive);
    tempBoard = new AboveImage(new EmptyImage(), rowImage);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.blue).movePinhole(0, game1.cellDimension / 2);
    cellSix = baseCellImage.movePinhole(0, -game1.cellDimension / 2);
    rowImage = new BesideImage(new EmptyImage(), cellSix);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.blue).movePinhole(0, game1.cellDimension / 2);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    baseCellImage = baseCellImage.movePinhole(game1.cellDimension / 2, 0);
    cellSeven = new OverlayImage(rightWall, baseCellImage).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellSeven);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        new Color(173, 216, 230)).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    cellEight = new OverlayImage(bottomWall, baseCellImage).movePinhole(0,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellEight);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        new Color(173, 216, 230)).movePinhole(0, game1.cellDimension / 2);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    baseCellImage = baseCellImage.movePinhole(game1.cellDimension / 2, 0);
    cellNine = new OverlayImage(rightWall, baseCellImage).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellNine);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.white).movePinhole(0, game1.cellDimension / 2);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    baseCellImage = baseCellImage.movePinhole(game1.cellDimension / 2, 0);
    cellTen = new OverlayImage(rightWall, baseCellImage).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellTen);
    tempBoard = new AboveImage(tempBoard, rowImage);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        new Color(173, 216, 230)).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    walls = new OverlayImage(bottomWall, baseCellImage).movePinhole(game1.cellDimension / 2, 0);
    cellEleven = new OverlayImage(rightWall, walls).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(new EmptyImage(), cellEleven);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.blue).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    cellTwelve = new OverlayImage(bottomWall, baseCellImage).movePinhole(0,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellTwelve);
    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.blue).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    cellThirteen = new OverlayImage(bottomWall, baseCellImage).movePinhole(0,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellThirteen);

    // cell 2,3

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.blue).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    cellFourteen = new OverlayImage(bottomWall, baseCellImage).movePinhole(0,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellFourteen);

    // cell 2,4

    baseCellImage = new RectangleImage(game1.cellDimension, game1.cellDimension, OutlineMode.SOLID,
        Color.blue).movePinhole(0, game1.cellDimension / 2);
    bottomWall = new LineImage(new Posn(game1.cellDimension, 0), Color.black);
    rightWall = new LineImage(new Posn(0, game1.cellDimension), Color.black).movePinhole(0,
        game1.cellDimension / 2);
    walls = new OverlayImage(bottomWall, baseCellImage).movePinhole(game1.cellDimension / 2, 0);
    cellFifteen = new OverlayImage(rightWall, walls).movePinhole(-game1.cellDimension / 2,
        -game1.cellDimension / 2);
    rowImage = new BesideImage(rowImage, cellFifteen);
    tempBoard = new AboveImage(tempBoard, rowImage);
    tempBoard = new OverlayImage(new RectangleImage(game1.cellDimension * game1.width,
        game1.cellDimension * game1.height, OutlineMode.OUTLINE, Color.black), tempBoard);

    t.checkExpect(game1.makeScene(), game1.gameBoard);

  }

  // to test the utilities class method posnEqual
  void testPosnEqual(Tester t) {
    this.initTestExamples();
    t.checkExpect(new Utils().posnEqual(new Posn(0, 0), new Posn(0, 0)), true);
    t.checkExpect(new Utils().posnEqual(new Posn(0, 0), new Posn(0, 1)), false);
    t.checkExpect(new Utils().posnEqual(new Posn(1, 0), new Posn(0, 1)), false);
    t.checkExpect(new Utils().posnEqual(new Posn(0, 1), new Posn(1, 0)), false);
    t.checkExpect(new Utils().posnEqual(new Posn(176, 114), new Posn(16, 10)), false);
    t.checkExpect(new Utils().posnEqual(new Posn(16, 13), new Posn(13, 16)), false);

  }

  // creates game
  void testMazeGame(Tester t) {
    MazeWorld game1 = new MazeWorld(5, 3, 15);
    game1.initBoard();
    game1.initEdges();
    game1.mst = game1.generateMaze();
    game1.bigBang(game1.getWidth(), game1.getHeight(), 0.0001);

  }
}