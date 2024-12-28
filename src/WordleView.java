import java.util.Observer;
import javax.swing.*;
import java.awt.*;

/**
 *
 * @author Aurora
 */

/**
 * The WordleView class represents the view component of the Wordle game.
 * It displays the game panels and updates them based on the model state.
 * It implements the Observer interface to receive updates from the model.
 */
public class WordleView implements Observer {
   
    private final WordleModel model;
    private final WordleController controller;
    
    private JFrame frame;
    private WordlePanel basePanel;
    private WordlePanel keyboardPanel;
    private WordlePanel MiddlePanel;

    private JPanel panel;

    /**
     * Constructs a WordleView object with the specified model and controller.
     * Registers itself as an observer of the model.
     * Initializes and creates the view components.
     *
     * @param model      the WordleModel object representing the game model
     * @param controller the WordleController object representing the game controller
     */
    public WordleView(WordleModel model, WordleController controller){
        
        this.model = model;
        model.addObserver(this);
        this.controller = controller;
        createAndInitControls();
        controller.setView(this);
        update(model, null); // Add model as observerable
    }

    /**
     * Creates and initializes the view components, including the JFrame and panels.
     * Sets the layout and adds the necessary components to the content pane.
     * Makes the frame visible.
     */
    public void createAndInitControls(){
        ImageIcon icon1 = new ImageIcon("src/icon/icon1.png", "Wordle Game");
        frame = new JFrame("WordleGame");
        frame.setIconImage(icon1.getImage());
        frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
        Container contentPane = frame.getContentPane(); 
        contentPane.setLayout(new BoxLayout(contentPane, BoxLayout.Y_AXIS));
        
        // Initialize Panels
        panel = new JPanel(new FlowLayout());
        panel.setBorder(BorderFactory.createEmptyBorder(10, 0, 10, 0));
        contentPane.add(panel);
        ImageIcon icon2 = new ImageIcon("src/icon/icon2.png");
        JLabel Imagelabel = new JLabel(icon2);
        panel.add(Imagelabel);
        MiddlePanel = new CrosswordPanel(model, controller);
        contentPane.add(MiddlePanel);
        keyboardPanel = new KeyboardPanel(model, controller);
        contentPane.add(keyboardPanel);
        basePanel = new BasePanel(model, controller);
        contentPane.add(basePanel);
        
        frame.pack(); 
        frame.setLayout(null);
        frame.setResizable(false);
        frame.setVisible(true);
    }

    /**
     * This method is called when the observed model notifies the observer.
     * It updates the state of the game panels and repaints the frame.
     *
     * @param o   the observable object (WordleModel)
     * @param arg an argument passed to the notifyObservers method (not used here)
     */
    @Override
    public void update(java.util.Observable o, Object arg){
        MiddlePanel.updateState();
        keyboardPanel.updateState();
        basePanel.updateState();
        frame.repaint();
    }
}
