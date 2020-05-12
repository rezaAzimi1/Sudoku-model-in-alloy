abstract sig Box{}
one sig b1,b2,b3,b4 /*,b5,b6,b7,b8,b9 */ extends Box{}
enum Number {One,two,there,four/*,five,six,seven,egite,nine*/}
sig sel {
box : one Box,
num:one Number,
//
up:lone sel,
down:lone sel,
left:lone sel,
right:lone sel,
}
//
//
fact {
// Number of cells per box
	all b:Box | #(box.b)=4
// The number of cells in each row means the cell up or down or the left and right cells of the cell minus one
	all s:sel | #((s.^right) + (s.^left))=3 and #((s.^up) + (s.^down))=3 
//
	all s:sel | (s.^left).left != s and (s.^left).up != s and (s.^left).down != s and    (s.^right).up != s and (s.^right).down != s and (s.^right).right != s and     (s.^up).left != s and (s.^up).up != s and (s.^up).right != s and        (s.^down).left != s and (s.^down).down != s and (s.^down).right != s 
// The difference in the number of cells in each box
	all a,b:sel | ( a != b and a.box = b.box )=>a.num != b.num
// Violation of top-down relationships left and right
	all s:sel | s.up = down.s and up.s = s.down and  s.right = left.s and right.s = s.left 
//
// No sharing between right and left
//	all s:sel | no (s.^right) & (s.^left) & (s.^up) & (s.^down)
	all s:sel | no (s.^right) & (s.^left) or no (s.^up) & (s.^down) or no (s.^up) & (s.^left) or no (s.^right) & (s.^down)or no (s.^up) & (s.^right) or no (s.^down) & (s.^left)
//

// The uniqueness of the cell itself, whether vertical or horizontal
	all s:sel | s !in ((s.^right) + (s.^left)+(s.^up) + (s.^down)) 
//The unity of the cell number, whether vertical or horizontal
	all s:sel | s.num !in ((s.^right) + (s.^left)+(s.^up) + (s.^down)).num
//!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
	//all s:sel,b:Box | s.box in b => ((s.up).box + (s.right).box ) in b and ((s.up).box  + (s.left).box ) in b and ((s.down).box + (s.right).box ) in b and ((s.down).box + (s.left).box ) in b
// Photo of cell signature relationships
all s:sel | lone up.s and lone down.s and lone left.s and lone right.s 
//
all s:sel |no ((s.^up) + (s.^down)) &((s.^right) + (s.^left))
	// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
//all s:sel | one s.left=>(s.^up).left + s.left + (s.^down).left=s.left+(s.left).^up+(s.left).^down or one s.right=>(s.^up).right + s.right + (s.^down).right=s.right+(s.right).^up+(s.right).^down or one s.up=> (s.^left).up + s.up + (s.^right).up=s.up+(s.up).^left+(s.up).^right or one s.down=>(s.^left).down + s.down + (s.^right).down=s.down+(s.down).^left+(s.down).^right
//
// Square and column trimming
all s:sel , p:{s.^up} |#(s.^right)=#(p.^right)
all s:sel , p:{s.^up} |#(s.^left)=#(p.^left)
all s:sel , p:{s.^down} |#(s.^right)=#(p.^right)
all s:sel , p:{s.^down} |#(s.^left)=#(p.^left)

all s:sel , p:{s.^left} |#(s.^up)=#(p.^up)
all s:sel , p:{s.^left} |#(s.^down)=#(p.^down)
all s:sel , p:{s.^right} |#(s.^up)=#(p.^up)
all s:sel , p:{s.^right} |#(s.^down)=#(p.^down)

// Limit box cells in each row of Weston
all s:sel,b:Box | s.box=b =>( #(((s.^left)+(s.^right)).box & b)=1 and #(((s.^up)+(s.^down)).box & b)=1)
//Sticky of boxes
all s:sel,b:Box |s.box = b =>(((s.left).box != b) =>no ((s.left).^left).box & b)
all s:sel,b:Box |s.box = b =>(((s.right).box != b) =>no ((s.right).^right).box & b)
all s:sel,b:Box |s.box = b =>(((s.up).box != b) =>no ((s.up).^up).box & b)
all s:sel,b:Box |s.box = b =>(((s.down).box != b) =>no ((s.down).^down).box & b)
}
run {} for 16
