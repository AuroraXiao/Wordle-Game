import java.awt.Color;
import java.awt.Dimension;
import java.awt.event.ActionEvent;
import javax.swing.*;
import javax.swing.border.*;

/**
 *
 * @author Aurora
 */
/** CLASS INVARIANT: keyboardLayout letters need to exist in model.availableLetters*/
public class KeyboardPanel extends WordlePanel {

    // Constants
    //@ public static invariant OUTLINE != null;
    public static Color OUTLINE = new Color(211, 214, 218);

    // Instance variables
    //@ private invariant KEYBOARD_LAYOUT != null && !KEYBOARD_LAYOUT.isEmpty();
    private final String KEYBOARD_LAYOUT;
    private JButton[] keyboardButtons;
    private int backspaceKeyIndex = 19, enterKeyIndex = 27;

    /**
     * Creates a new KeyboardPanel with the specified WordleModel and WordleController.
     *
     * @param model      the WordleModel associated with this panel
     * @param controller the WordleController associated with this panel
     * @throws IllegalArgumentException if the model or controller is null
     */
    //@ requires model != null;
    //@ requires controller != null;
    public KeyboardPanel(WordleModel model, WordleController controller){
        super(model, controller);
        super.panelSize = new Dimension(580, 190);
        KEYBOARD_LAYOUT = "QWERTYUIOPASDFGHJKLZXCVBNM";
        initKeyboard();
        createKeyboardPanel();
    }

    /**
     * Updates the state of the keyboard buttons based on the WordleModel's available letters.
     */
    //@ ensures \forall int i; 0 <= i && i < keyboardButtons.length;
    //@     (\exists char c; c == keyboardButtons[i].getText().toLowerCase().charAt(0);
    //@         i != enterKeyIndex && i != backspaceKeyIndex) ==>
    //@             changeKeyState(keyboardButtons[i], wordleModel.getAvailableLetters().get(c));
    @Override
    public void updateState(){
        JButton key; char c;
        for(int i = 0 ; i < keyboardButtons.length;i++){
            key = keyboardButtons[i];
            c = key.getText().toLowerCase().charAt(0);
            if(i != enterKeyIndex && i != backspaceKeyIndex)
                changeKeyState(key, wordleModel.getAvailableLetters().get(c));
        }
    }

    private void initKeyboard(){
        /*ImageIcon backspace = new ImageIcon("src/Icon/backspace1.png");*/
        /*String backspace = Character.toString((char)9003);*/
        String backspace = "Backspace";
        String enter = "Enter";
        keyboardButtons = new JButton[KEYBOARD_LAYOUT.length()+2];
        // x iteratrates through keyboardLayout array
        // i iteratrates through keyboardButtons array
        for (int i = 0, x = 0; i < keyboardButtons.length; i++){
            if (i == enterKeyIndex)
                keyboardButtons[i] = createKeyboardButton(enter);
            else if (i == backspaceKeyIndex)
                keyboardButtons[i] = createKeyboardButton(backspace);
            else{
                keyboardButtons[i] = createKeyboardButton(Character.toString(
                        KEYBOARD_LAYOUT.charAt(x)));
                x++; 
            }
        }
    }
    
    private void createKeyboardPanel() {
        for(int i = 0 ; i < keyboardButtons.length;i++){
            //@ assert i >= 0 && i < keyboardButtons.length;
            //@ assert keyboardButtons != null;
            //@ assert keyboardButtons[i] != null;
            if(i == enterKeyIndex){
                keyboardButtons[i].addActionListener((ActionEvent e) -> {
                    //@ assert e != null;
                    wordleController.submitGuess();});
            }
            else if(i == backspaceKeyIndex){
                keyboardButtons[i].addActionListener((ActionEvent e) -> {
                    wordleController.removeFromGuess();});
            }
            else{
                keyboardButtons[i].addActionListener((ActionEvent e) -> {
                    String buttonText = ((JButton)e.getSource()).getText();
                    wordleController.addToGuess(buttonText);});
            }
        }
        // Add KeyButtons to Panel
        //@ loop_invariant 0 <= i && i <= keyboardButtons.length;
        for(int i = 0 ; i < keyboardButtons.length;i++)
            //@ assert i >= 0 && i < keyboardButtons.length;
            //@ assert keyboardButtons != null;
            //@ assert keyboardButtons[i] != null;
            this.add(keyboardButtons[i]);
    }
    
    private JButton createKeyboardButton(String text) {
        JButton button = new JButton(text);
        changeKeyState(button, wordleModel.NO_STATE);
        Border margin = new EmptyBorder(17, 20, 17, 20);
        Border compound = new CompoundBorder(null, margin);
        button.setBorder(compound);
        return button;
    }
    
    private void changeKeyState(JButton key, int state){
        if(state == wordleModel.NO_STATE)
            /*changeKeyColor(key, Color.BLACK, Color.LIGHT_GRAY);*/
            changeKeyColor(key, Color.BLACK, OUTLINE);
        else if (state == wordleModel.GREEN_STATE)
            changeKeyColor(key, Color.WHITE, GREEN);
        else if (state == wordleModel.YELLOW_STATE)
            changeKeyColor(key, Color.WHITE, YELLOW);
        else if (state == wordleModel.GREY_STATE)
            changeKeyColor(key, Color.WHITE, Color.DARK_GRAY);
    }
    
    private void changeKeyColor(JButton key, Color fontColor, Color backgroundColor){
        key.setForeground(fontColor);
        key.setBackground(backgroundColor);
    }
}
