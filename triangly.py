import math
import random
import matplotlib.pyplot as plt
import itertools
from shapely.geometry import Point, MultiPoint, LineString

def pointdistance(p1, p2):
    return math.sqrt((p1[0] - p2[0]) ** 2 + (p1[1] - p2[1]) ** 2)

def getAngle(a, b, c):  # finds angle in degrees between these three points at b, taken clockwise
    ang = math.degrees(math.atan2(c[1] - b[1], c[0] - b[0]) - math.atan2(a[1] - b[1], a[0] - b[0]))
    return ang

def findIntersection(A, B, C, D): #intersection of line through A,B with line through C,D
    px = ((A[0] * B[1] - A[1] * B[0]) * (C[0] - D[0]) - (A[0] - B[0]) * (C[0] * D[1] - C[1] * D[0])) / (
                (A[0] - B[0]) * (C[1] - D[1]) - (A[1] - B[1]) * (C[0] - D[0]))
    py = ((A[0] * B[1] - A[1] * B[0]) * (C[1] - D[1]) - (A[1] - B[1]) * (C[0] * D[1] - C[1] * D[0])) / (
                (A[0] - B[0]) * (C[1] - D[1]) - (A[1] - B[1]) * (C[0] - D[0]))
    return [px, py]

def FindCircle(p1,p2,p3): #finds circle given three points on it. Output is centre, radius
    if p2[0] == p1[0]:
        m1 = 0
    else:
        m1 = (p1[0] - p2[0])/(p2[1] - p1[1]) # negative reciprocal of gradient of line through p1 and p2
    if p3[0] == p1[0]:
        m2 = 0
    else:
        m2 = (p1[0] - p3[0])/(p3[1] - p1[1]) # negative reciprocal of gradient of line through p1 and p2
    midpoint1 = [(p1[0]+p2[0])/2,(p1[1]+p2[1])/2]
    midpoint2 = [(p1[0]+p3[0])/2,(p1[1]+p3[1])/2]
    centre = findIntersection(midpoint1, [midpoint1[0]+1,midpoint1[1]+m1],midpoint2, [midpoint2[0]+1,midpoint2[1]+m2])
    radius = pointdistance(centre,p1)
    return centre,radius

def circle_line_segment_intersection(circle_center, circle_radius, pt1, pt2, full_line=True, tangent_tol=1e-9):
    """ Find the points at which a circle intersects a line-segment.  This can happen at 0, 1, or 2 points.

    :param circle_center: The (x, y) location of the circle center
    :param circle_radius: The radius of the circle
    :param pt1: The (x, y) location of the first point of the segment
    :param pt2: The (x, y) location of the second point of the segment
    :param full_line: True to find intersections along full line - not just in the segment.  False will just return intersections within the segment.
    :param tangent_tol: Numerical tolerance at which we decide the intersections are close enough to consider it a tangent
    :return Sequence[Tuple[float, float]]: A list of length 0, 1, or 2, where each element is a point at which the circle intercepts a line segment.

    Note: We follow: http://mathworld.wolfram.com/Circle-LineIntersection.html
    """

    (p1x, p1y), (p2x, p2y), (cx, cy) = pt1, pt2, circle_center
    (x1, y1), (x2, y2) = (p1x - cx, p1y - cy), (p2x - cx, p2y - cy)
    dx, dy = (x2 - x1), (y2 - y1)
    dr = (dx ** 2 + dy ** 2)**.5
    big_d = x1 * y2 - x2 * y1
    discriminant = circle_radius ** 2 * dr ** 2 - big_d ** 2

    if discriminant < 0:  # No intersection between circle and line
        return []
    else:  # There may be 0, 1, or 2 intersections with the segment
        intersections = [
            (cx + (big_d * dy + sign * (-1 if dy < 0 else 1) * dx * discriminant**.5) / dr ** 2,
             cy + (-big_d * dx + sign * abs(dy) * discriminant**.5) / dr ** 2)
            for sign in ((1, -1) if dy < 0 else (-1, 1))]  # This makes sure the order along the segment is correct
        if not full_line:  # If only considering the segment, filter out intersections that do not fall within the segment
            fraction_along_segment = [(xi - p1x) / dx if abs(dx) > abs(dy) else (yi - p1y) / dy for xi, yi in intersections]
            intersections = [pt for pt, frac in zip(intersections, fraction_along_segment) if 0 <= frac <= 1]
        if len(intersections) == 2 and abs(discriminant) <= tangent_tol:  # If line is tangent to circle, return just one point (as both intersections have same location)
            return [intersections[0]]
        else:
            return intersections

def ray_tracing_method(x, y, poly):  # returns true if x,y is in poly

    n = len(poly)
    inside = False

    p1x, p1y = poly[0]
    for i in range(n + 1):
        p2x, p2y = poly[i % n]
        if y > min(p1y, p2y):
            if y <= max(p1y, p2y):
                if x <= max(p1x, p2x):
                    if p1y != p2y:
                        xints = (y - p1y) * (p2x - p1x) / (p2y - p1y) + p1x
                    if p1x == p2x or x <= xints:
                        inside = not inside
        p1x, p1y = p2x, p2y

    return inside

def TriangleContains(p1,p2,p3,points):
    interior = []
    for x in points:
        if x not in [p1,p2,p3]:
            if ray_tracing_method(x[0],x[1],[p1,p2,p3]):
                test_point = Point(x)
                line1 = LineString([p1, p2])
                line2 = LineString([p1, p3])
                line3 = LineString([p2, p3])

                if (not line1.distance(test_point) < 1e-8 and not line2.distance(test_point) < 1e-8) and not line3.distance(test_point) < 1e-8:
                    interior.append(x)
    return interior

def find_angle(p1, p2):  # finds angle in degrees of p2 from p1, 0 degrees is parallel to the x-axis, to the right
    rise = p2[1] - p1[1]
    run = p2[0] - p1[0]
    if run == 0:
        if rise == 0:
            return
        if rise > 0:
            return 90
        if rise < 0:
            return 270
    else:
        return math.degrees(math.atan2(rise, run))

def ApexCollection(z,u,v,x,y,terms,centre,radius): # u is whichever side you're starting at
    terms_by_apex = []
    for t in terms:
        if t not in [u,v,x,y]:
            attempt_list = []
            if len(z[2]) == 2:
                a = circle_line_segment_intersection(centre, radius, x, t)
                b = circle_line_segment_intersection(centre, radius, y, t)
                print(a,b)
                if len(a) > 0:
                    for item in a:
                        attempt_list.append(item)
                if len(b) > 0:
                    for item in b:
                        attempt_list.append(item)
            else:
                a = findIntersection(u,v,x,t)
                b = findIntersection(u, v, y, t)
                attempt_list.append(findIntersection(u,v,x,t))
                attempt_list.append(findIntersection(u, v, y, t ))
            if len(attempt_list) > 0:
                for item in attempt_list:
                    if is_point_on_arc(z,u,v,centre,item) and item not in terms_by_apex:
                        terms_by_apex.append(list(item))
    terms_by_apex.sort(key=lambda item: pointdistance(u,findIntersection(u,v,item,centre)))
    return(terms_by_apex)

def first_and_last_empty_triangle(u,v,x,y,rel_terms,apexes):
    full_testers = [u]+apexes+[v]
    successes = []
    for apex in full_testers:
        if len(TriangleContains(apex, x, y, rel_terms)) == 0:
            successes.append(apex)
    if len(successes) > 0:
        return [successes[0],successes[-1]]
    else:
        return False

def same_side(u, v, x, y):  # returns true if both u and v are on the same side of x and y
    if y[0] == x[0]:
        return (u[0] <= x[0] and v[0] <= x[0]) or (u[0] >= x[0] and v[0] >= x[0])
    else:
        m = (y[1] - x[1]) / (y[0] - x[0])
        return ((u[1] - m * u[0] >= x[1] - m * x[0]) and (v[1] - m * v[0] >= x[1] - m * x[0])) or (
                    (u[1] - m * u[0] <= x[1] - m * x[0]) and (v[1] - m * v[0] <= x[1] - m * x[0]))


def is_point_on_arc(z_point,u,v, centre, point_in_question):  # checks if point in question is in cone of z_point
    return same_side(centre, point_in_question,z_point,u) and same_side(centre, point_in_question,z_point,v)

n = 5

uu = [0.675, 0.5]
vv = [0.5, 0.675]
zz = [0.75, 0.75,[[1],[2],[3]]]
xx = [0,0.375]
yy = [0.5,0]

# aa = [0.49,0.49]
# bb = [0.6,0.4]

centre1,radius1 = FindCircle(uu,vv,zz)

spec_points = [uu,vv,zz,xx,yy]

bonus_points = []

for i in range(n):
    bonus_points.append([random.random(), random.random()])

all_points = spec_points + bonus_points

relevant_terminals = []

hull = MultiPoint([uu,vv,xx,yy]).convex_hull

for terminal in all_points:
    if hull.contains(Point(terminal[:2])):
        relevant_terminals.append(terminal)

print("Relevant ones are: ",relevant_terminals)

apexes_on_curve = ApexCollection(zz,uu,vv,xx,yy,relevant_terminals,centre1,radius1)

apexes_found = first_and_last_empty_triangle(uu,vv,xx,yy,relevant_terminals,apexes_on_curve)

print("RESULT WAS ",apexes_found)

fig, ax = plt.subplots()

xs = [point[0] for point in all_points]  # this part is for plotting the points
ys = [point[1] for point in all_points]
plt.scatter(xs, ys)

if apexes_found != False:
    ws = [point[0] for point in apexes_found]  # this part is for plotting the points
    zs = [point[1] for point in apexes_found]
    plt.scatter(ws, zs,color='g')


for i in range(len(spec_points)):
    ax.annotate(i, (xs[i], ys[i]))

circle1 = plt.Circle(centre1, radius1, color='r',fill=False)
plt.gca().add_patch(circle1)

if apexes_on_curve != False:
    apexes_on_curve = apexes_on_curve + [uu,vv]
else:
    apexes_on_curve = [[uu], [vv]]

print("POSSIBLE APEXES WERE ",apexes_on_curve)

for point in apexes_on_curve:
    for edge in itertools.combinations([xx,point,yy],2):
        x = [edge[0][0], edge[1][0]]
        y = [edge[0][1], edge[1][1]]
        plt.plot(x, y, 'b')

ax.set_xlim([0, 1])
ax.set_ylim([0, 1])
ax.set_aspect('equal')
plt.show()