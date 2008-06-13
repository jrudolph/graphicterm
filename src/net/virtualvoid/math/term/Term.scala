package net.virtualvoid.math.term

trait Exp{
  def tryTrans(t:Trans):Exp = 
    if (t.pre(this))
      t(this)
    else 
      this
  
  def *(exp:Exp) = Apply(this,Ops.*,exp)
  def +(exp:Exp) = Apply(this,Ops.Add,exp)
  def -(exp:Exp) = Apply(this,Ops.-,exp)
  def /(exp:Exp) = Apply(this,Ops./,exp)
}

trait Trans extends (Exp=>Exp){
  def pre(e:Exp):Boolean
}

trait Op{
  override def toString = getClass.getSimpleName
  def calc(a:Int,b:Int):Int
}
object Ops{
	object * extends Op{
	  override def toString="*"
	  def calc(a:Int,b:Int) = a*b
	}
	object Add extends Op{
	  override def toString="+"
	  def calc(a:Int,b:Int) = a+b
	}
    object - extends Op{
	  override def toString="-"
	  def calc(a:Int,b:Int) = a-b
	}
	object / extends Op{
	  override def toString="/"
	  def calc(a:Int,b:Int) = a/b
	}
}
import Ops._
case class Symbol(name:String) extends Exp{
  override def toString=name
}
case class Integer(i:Int) extends Exp{
  override def toString=i.toString
}
object Helper{
  implicit def int2Int(i:Int):Integer = Integer(i)
  implicit def str2symbol(s:String):Symbol = Symbol(s)
}
import Helper._

case class Apply(left:Exp,operator:Op,right:Exp) extends Exp{
  override def toString="(" + left.toString +" "+ operator.toString + " " + right.toString + ")"
}

class Commutative(op:Op) extends Trans{
  def pre(e:Exp) = e match {case Apply(_,o,_) if o==op =>true;case _=>false}
  def apply(e:Exp) = e match {case Apply(a,o,b) if o==op =>Apply(b,op,a)}
}

class Associative(op:Op) extends Trans{
  def pre(e:Exp) = e match {
  case Apply(Apply(_,o,_),o2,_) if o==op && o2==op =>true;
  case Apply(_,o2,Apply(_,o,_)) if o==op && o2==op =>true;
  case _=>false}
  def apply(e:Exp) = e match {
  case Apply(Apply(a,o,b),o2,c) if o==op && o2==op => Apply(a,op,Apply(b,op,c))
  case Apply(a,o2,Apply(b,o,c)) if o==op && o2==op => Apply(Apply(a,o,b),o2,c)
  } 
}

object MultCom extends Commutative(*);
object AddCom extends Commutative(Add);
object AddAss extends Associative(Add);
object MultAss extends Associative(*);

object CoeffExp{
  def unapply(exp:Exp):Option[(Int,Exp)] = exp match {
  case Apply(Integer(i2),*,e2:Exp) => Some(i2,e2)
  case e:Symbol => Some(1,exp)
  case _ => Some(1,exp)
  }
}

object Collect extends Trans{
  def pre(e:Exp) = e match {
    case Apply(s1,Add,s2) if s1 == s2 => true
    case Apply(CoeffExp(i,e1),Add,CoeffExp(i2,e2)) if e1 == e2 => true
    case _=>false
  }
  def apply(e:Exp) = e match {
    case Apply(s1,Add,s2) if s1 == s2 => Apply(Integer(2),*,s1)
    case Apply(CoeffExp(i,e1),Add,CoeffExp(i2,e2)) if e1 == e2 => Apply(Integer(i+i2),*,e1) 
  }
}

object Distribute extends Trans{
  def pre(e:Exp) = e match {
  case Apply(_,*,Apply(_,Add,_)) => true
  case Apply(_,*,Apply(_,-,_)) => true
  case _ => false
  }
  def apply(e:Exp) = e match {
  case Apply(x,*,Apply(s1,Add,s2)) => Apply(Apply(x,*,s1),Add,Apply(x,*,s2))
  case Apply(x,*,Apply(s1,-,s2)) => Apply(Apply(x,*,s1),Ops.-,Apply(x,*,s2))
  }
}

object Calc extends Trans{
  def pre(e:Exp) = e match {
  case Apply(Integer(i1),op,Integer(i2)) if Array(Add,*).contains(op)=> true
  case _ => false
  }
  def apply(e:Exp) = e match{
  case Apply(Integer(i1),op,Integer(i2)) if Array(Add,*).contains(op)=> Integer(op.calc(i1,i2))
  }
}

object AntiDistribute extends Trans {
  def pre(e:Exp) = e match {
  case Apply(Apply(s1,*,x1),Add,Apply(s2,*,x2)) if s1==s2 => true
  case _ => false
  }
  def apply(e:Exp) = e match {
  case Apply(Apply(s1,*,x1),Add,Apply(s2,*,x2)) if s1==s2 => Apply(s1,*,Apply(x1,Add,x2))
  }
}

object Introduce1 extends Trans {
  def pre(e:Exp) = true
  def apply(e:Exp) = Apply(1,*,e)
}


case class ExpZipper(exp:Exp){
  def left = exp match {case Apply(left,_,_)=>LeftZipper(this,left)}
  def right = exp match {case Apply(_,_,right)=>RightZipper(this,right)}
  def replace(e:Exp) = e
  def tryTrans(t:Trans):Exp = replace(exp.tryTrans(t))
}
abstract case class ParentalZipper(parent:ExpZipper,override val exp:Exp)extends ExpZipper(exp){
  override def replace(e:Exp):Exp = parent match {
      case ExpZipper(exp:Apply) => 
	    parent.replace(reconstructParent(e,exp))
  }
  def reconstructParent(e:Exp,ap:Apply):Apply
}
case class LeftZipper(override val parent:ExpZipper,override val exp:Exp) extends ParentalZipper(parent,exp){
  def reconstructParent(e:Exp,ap:Apply) = Apply(e,ap.operator,ap.right)
}
case class RightZipper(override val parent:ExpZipper,override val exp:Exp) extends ParentalZipper(parent,exp){
  def reconstructParent(e:Exp,ap:Apply) = Apply(ap.left,ap.operator,e)
}

import java.awt.font.FontRenderContext
import java.awt.Font
class Layouter(f:Font,ctx:FontRenderContext){
  import java.awt.font._
  import java.text._
  
  val space = 10d
  
  def layout(s:String) = new TextLayout(s,f,ctx)
  
  def width(op:Op) = layout(op.toString).getAdvance
  
  def width(e:Exp):Double = e match {
  case Apply(e1,/,e2) => 2*space + width(e1).max(width(e2))  
  case Apply(e1,op,e2) => layout("(+)").getAdvance + width(e1) + width(e2) + 4 * space
  case _ => layout(e.toString).getAdvance
  }
  def height(e:Exp):Double = (e match {
  case Apply(e1,/,e2) => 2*space + height(e1) + height(e2)
  case Apply(e1,op,e2) => layout("(+)").getBounds.getHeight.max(height(e1).max(height(e2)))
  case _ => layout(e.toString).getBounds.getHeight
  }) + 2 * space
  
  def offsetLeft(ap:Apply):(Double,Double) = ap match {
  case Apply(e1,/,e2) => (width(ap)/2-width(e1)/2,-space-height(e1)/2)
  case _ => (space+layout("(").getAdvance,0)
  }
    
  def offsetRight(ap:Apply):(Double,Double) = ap match{
  case Apply(e1,/,e2) => (width(ap)/2-width(e2)/2,space+height(e2)/2)    
  case _ => (4*space + width(ap.left) + width(ap.operator),0)
  }
  
  import java.awt.Graphics2D
  
  def drawString(g2d:Graphics2D,s:String,x:Double,y:Double){
    val lo = layout(s)
    g2d.drawString(s,x.toFloat,(y+lo.getAscent/2).toFloat)
  }
  
  def getAt(cur:ExpZipper,x:Double,y:Double):Option[ExpZipper] = {
    val root = cur.exp
    val h = height(root)
    if (x<0||x>width(root)||y< -h/2||y>h/2)
      None
    else
      cur match{
      case pos@ExpZipper(a@Apply(e1,op,e2)) => {
        val ol = offsetLeft(a)
        val or = offsetRight(a)
        
        getAt(pos.left,x-ol._1,y-ol._2).orElse(getAt(pos.right,x-or._1,y-or._2)).orElse(Some(cur))
      }
      case _ => Some(cur)
      }
  }
  
  def draw(g2d:Graphics2D,cur:ExpZipper,x:Double,y:Double)(implicit over:Option[ExpZipper],selected:scala.collection.mutable.Set[ExpZipper]){
    val h=height(cur.exp)
    val w=width(cur.exp)
    
    val oldColor = g2d.getColor
    over.foreach(sel => if (sel == cur) {
      g2d.setColor(new java.awt.Color(177,177,255,150))
      g2d.fillRect(x.toInt,(y-h/2).toInt,w.toInt,h.toInt)
    })
    if (selected.contains(cur)){
      g2d.setColor(new java.awt.Color(0,149,1,100))
      g2d.fillRect(x.toInt,(y-h/2).toInt,w.toInt,h.toInt)
    }
    g2d.setColor(oldColor)
    cur match{
  case pos@ExpZipper(a@Apply(e1,/,e2)) => {
    val ol = offsetLeft(a)
    val or = offsetRight(a)

    draw(g2d,pos.left,x+ol._1,y+ol._2)
    draw(g2d,pos.right,x+or._1,y+or._2)
    
    g2d.drawLine(x.toInt,y.toInt,(x+width(cur.exp)).toInt,y.toInt)
  }
  case pos@ExpZipper(a:Apply) => {
    val ol = offsetLeft(a)
    val or = offsetRight(a)
    drawString(g2d,"(",x,y)
    draw(g2d,pos.left,x+ol._1,y+ol._2)
    drawString(g2d,a.operator.toString,x+ol._1+width(a.left)+space,y)
    draw(g2d,pos.right,x+or._1,y+or._2)
    drawString(g2d,")",x+or._1+space+width(a.right),y)
  }
  case _ => {
    val h = height(cur.exp)
    drawString(g2d,cur.exp.toString,x,y)
  }}}
}

object Test{
  import javax.swing._
  import java.awt.event._
  def showFrame:JFrame = {    
    val frame = new JFrame
    frame.setSize(500,500)
    frame.setTitle("Expression Viewer")
    frame.setVisible(true)
    
    frame.addWindowListener(new WindowAdapter(){
      override def windowClosing(e:WindowEvent) {
        System.exit(0);
      }
    })
    frame
  }
  def main(args:Array[String]) {
	val x = Symbol("x")
	val y = Symbol("y")
	
	val term = Apply(Apply(x,Add,y),Add,y)
    System.out.println(term.tryTrans(AddAss).toString)
    
    val term2 = Apply(Integer(2),Add,Apply(Apply(Integer(3),*,y),/,Apply(Integer(2),*,y)))
    System.out.println(Collect.pre(term2).toString)
    System.out.println(term2.tryTrans(Collect).toString)
    
    val xy = x + y
    val term3 = Integer(2) * xy + xy
    System.out.println(Collect.pre(term3))
    System.out.println(term3.tryTrans(Collect))
    
    System.out.println(Collect.pre(xy))
    System.out.println(xy.tryTrans(Collect))
    
    val term4 = Apply(4,*,Apply(2,Add,Apply(4,*,3)))
    
    val e = Symbol("e")
    val w = Symbol("ω")
    val b = Symbol("β")
    val term5:Exp = Symbol("a") / (w * w) * e * (Integer(-1) * b *(Symbol("t") - "t0")) 
    
    val panel = showFrame
    val canvas = new JComponent{
      import java.awt.{Color,Graphics,Graphics2D,Font}
      var root:Exp = term5
      var over:Option[ExpZipper] = None
      val selected = scala.collection.mutable.Set[ExpZipper]()
      val font2 = new Font("Helvetica",Font.PLAIN,30)
      val lo = new Layouter(font2,new FontRenderContext(font2.getTransform,true,true))
      val yOffset = 200;
      
      addMouseMotionListener(new java.awt.event.MouseMotionAdapter(){
      override def mouseMoved(e:java.awt.event.MouseEvent){
        over = lo.getAt(ExpZipper(root),e.getX-50,e.getY-yOffset)
        repaint()
      }});
      
      addMouseListener(new java.awt.event.MouseAdapter(){
      override def mouseClicked(e:java.awt.event.MouseEvent){
        lo.getAt(ExpZipper(root),e.getX-50,e.getY-yOffset).foreach(sel => 
          if (selected.contains(sel)) selected-=sel else selected+=sel)
        repaint()
      }                
      })
      
      panel.addKeyListener(new java.awt.event.KeyAdapter(){
        def tryTrans(ts:Trans*) = {
          root = selected.elements.buffered.head.replace(
            ts.foldLeft(selected.elements.buffered.head.exp)
                     {(exp,t) => exp.tryTrans(t)})
          selected.clear
          repaint()
        }  
      override def keyPressed(e:java.awt.event.KeyEvent){
        import java.awt.event.KeyEvent._
        System.out.println(e.getKeyCode)
        if (e.getKeyCode == VK_K && selected.size == 1)
          tryTrans(AddCom,MultCom)
        else if (e.getKeyCode == VK_C && selected.size == 1)
          tryTrans(Collect)
        else if (e.getKeyCode == VK_D && selected.size == 1)
          tryTrans(Distribute)
        else if (e.getKeyCode == VK_A && selected.size == 1)
          tryTrans(MultAss,AddAss)
        else if (e.getKeyCode == VK_Q && selected.size == 1)
          tryTrans(AntiDistribute)
        else if (e.getKeyCode == VK_1 && selected.size == 1)
          tryTrans(Introduce1)
        else if (e.getKeyCode == VK_EQUALS && selected.size == 1)
          tryTrans(Calc)
      }
      })
      
      override def paint(g:Graphics) {
        val g2d = g.asInstanceOf[Graphics2D]
        over.foreach(exp => g2d.drawString(exp.exp.toString,0,50))
        g2d.setFont(font2)
        lo.draw(g2d,ExpZipper(root),50,yOffset)(over,selected)
      }
    }
    canvas.setSize(panel.getSize)
    panel.add(canvas)
  }
}